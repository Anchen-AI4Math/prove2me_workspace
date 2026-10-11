import Definitions.Def_Snaky21Data09
import Solutions.Snaky21.Geometry
import Solutions.Snaky21.Certificate08

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_inline_375 : inline_375 = combine (5, 5) [placed 4 (8, 4) card_0, placed 1 (4, 2) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_375 : Valid inline_375 := by
  rw [eq_inline_375]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 4) valid_0
  subst c
  exact placed_valid 1 (4, 2) valid_5

theorem eq_inline_376 : inline_376 = combine (3, 2) [placed 7 (4, 5) card_5, placed 5 (0, 5) card_87] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_376 : Valid inline_376 := by
  rw [eq_inline_376]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_5
  subst c
  exact placed_valid 5 (0, 5) valid_87

theorem eq_inline_377 : inline_377 = combine (4, 5) [inline_375, inline_376] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_377 : Valid inline_377 := by
  rw [eq_inline_377]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_375
  subst c
  exact valid_inline_376

theorem eq_inline_378 : inline_378 = combine (3, 2) [placed 5 (0, 5) card_87, placed 0 (1, 0) card_215] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_378 : Valid inline_378 := by
  rw [eq_inline_378]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_87
  subst c
  exact placed_valid 0 (1, 0) valid_215

theorem eq_inline_379 : inline_379 = combine (4, 2) [placed 0 (4, 1) card_52, placed 6 (5, 5) card_246, inline_377, inline_378] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_379 : Valid inline_379 := by
  rw [eq_inline_379]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 5) valid_246
  rcases hc with rfl | hc
  · exact valid_inline_377
  subst c
  exact valid_inline_378

theorem eq_card_576 : card_576 = combine (4, 3) [placed 6 (7, 4) card_5, inline_379] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_576 : Valid card_576 := by
  rw [eq_card_576]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 4) valid_5
  subst c
  exact valid_inline_379

theorem eq_inline_380 : inline_380 = combine (3, 1) [placed 0 (3, 0) card_15, placed 4 (4, 0) card_393] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_380 : Valid inline_380 := by
  rw [eq_inline_380]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_15
  subst c
  exact placed_valid 4 (4, 0) valid_393

theorem eq_inline_381 : inline_381 = combine (3, 3) [placed 0 (0, 2) card_0, inline_380] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_381 : Valid inline_381 := by
  rw [eq_inline_381]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_0
  subst c
  exact valid_inline_380

theorem eq_card_577 : card_577 = combine (4, 3) [placed 0 (1, 2) card_5, inline_381] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_577 : Valid card_577 := by
  rw [eq_card_577]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_5
  subst c
  exact valid_inline_381

theorem eq_card_578 : card_578 = combine (4, 3) [placed 0 (1, 2) card_26, placed 2 (1, 4) card_49, placed 0 (1, 0) card_117, placed 0 (0, 1) card_577] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_578 : Valid card_578 := by
  rw [eq_card_578]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_26
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 4) valid_49
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_117
  subst c
  exact placed_valid 0 (0, 1) valid_577

theorem eq_card_579 : card_579 = combine (3, 4) [placed 0 (0, 1) card_118, placed 2 (0, 6) card_137, placed 0 (0, 1) card_172, placed 0 (0, 1) card_173, placed 2 (0, 6) card_181, placed 2 (0, 7) card_435, placed 0 (0, 1) card_507, placed 0 (0, 1) card_578, placed 2 (0, 7) card_578] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_579 : Valid card_579 := by
  rw [eq_card_579]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_118
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_137
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_172
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_173
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_507
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_578
  subst c
  exact placed_valid 2 (0, 7) valid_578

theorem eq_card_580 : card_580 = combine (4, 2) [placed 0 (1, 1) card_24, placed 2 (1, 3) card_49, placed 1 (1, 1) card_194, placed 0 (0, 0) card_577] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_580 : Valid card_580 := by
  rw [eq_card_580]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_24
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 3) valid_49
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_194
  subst c
  exact placed_valid 0 (0, 0) valid_577

theorem eq_card_581 : card_581 = combine (4, 6) [placed 0 (2, 2) card_188, placed 4 (6, 2) card_188, placed 3 (7, 4) card_258, placed 7 (7, 7) card_309, placed 1 (1, 3) card_578, placed 3 (7, 3) card_578] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_581 : Valid card_581 := by
  rw [eq_card_581]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_258
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 7) valid_309
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_578
  subst c
  exact placed_valid 3 (7, 3) valid_578

theorem eq_inline_382 : inline_382 = combine (5, 6) [placed 1 (4, 3) card_5, placed 5 (1, 7) card_160] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_382 : Valid inline_382 := by
  rw [eq_inline_382]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 3) valid_5
  subst c
  exact placed_valid 5 (1, 7) valid_160

theorem eq_inline_383 : inline_383 = combine (4, 5) [placed 1 (2, 2) card_133, inline_382] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_383 : Valid inline_383 := by
  rw [eq_inline_383]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_133
  subst c
  exact valid_inline_382

theorem eq_inline_384 : inline_384 = combine (3, 6) [placed 5 (0, 7) card_12, placed 5 (0, 7) card_14, placed 1 (1, 3) card_109, placed 1 (1, 3) card_424] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_384 : Valid inline_384 := by
  rw [eq_inline_384]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_109
  subst c
  exact placed_valid 1 (1, 3) valid_424

theorem eq_inline_385 : inline_385 = combine (4, 5) [placed 7 (6, 6) card_383, placed 3 (5, 3) card_432] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_385 : Valid inline_385 := by
  rw [eq_inline_385]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_383
  subst c
  exact placed_valid 3 (5, 3) valid_432

theorem eq_card_582 : card_582 = combine (4, 6) [placed 5 (1, 7) card_184, placed 5 (1, 7) card_423, placed 0 (1, 0) card_572, inline_383, inline_384, inline_385] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_582 : Valid card_582 := by
  rw [eq_card_582]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_184
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_423
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_572
  rcases hc with rfl | hc
  · exact valid_inline_383
  rcases hc with rfl | hc
  · exact valid_inline_384
  subst c
  exact valid_inline_385

theorem eq_inline_386 : inline_386 = combine (9, 6) [placed 1 (5, 6) card_6, placed 2 (2, 10) card_576] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_386 : Valid inline_386 := by
  rw [eq_inline_386]
  apply combination_rule (9, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 6) valid_6
  subst c
  exact placed_valid 2 (2, 10) valid_576

theorem eq_inline_387 : inline_387 = combine (9, 6) [placed 5 (5, 6) card_6, placed 2 (2, 10) card_576] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_387 : Valid inline_387 := by
  rw [eq_inline_387]
  apply combination_rule (9, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 6) valid_6
  subst c
  exact placed_valid 2 (2, 10) valid_576

theorem eq_inline_388 : inline_388 = combine (8, 6) [placed 2 (5, 7) card_8, placed 2 (5, 10) card_321, inline_386, inline_387] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_388 : Valid inline_388 := by
  rw [eq_inline_388]
  apply combination_rule (8, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 7) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 10) valid_321
  rcases hc with rfl | hc
  · exact valid_inline_386
  subst c
  exact valid_inline_387

theorem eq_inline_389 : inline_389 = combine (5, 6) [placed 6 (7, 6) card_3, inline_388] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_389 : Valid inline_389 := by
  rw [eq_inline_389]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 6) valid_3
  subst c
  exact valid_inline_388

theorem eq_inline_390 : inline_390 = combine (5, 8) [placed 1 (2, 8) card_7, placed 1 (2, 5) card_86, placed 1 (2, 5) card_542] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_390 : Valid inline_390 := by
  rw [eq_inline_390]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 8) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_86
  subst c
  exact placed_valid 1 (2, 5) valid_542

theorem eq_inline_391 : inline_391 = combine (6, 7) [placed 4 (7, 5) card_48, placed 0 (3, 5) card_109, placed 4 (7, 5) card_246] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_391 : Valid inline_391 := by
  rw [eq_inline_391]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_48
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 5) valid_109
  subst c
  exact placed_valid 4 (7, 5) valid_246

theorem eq_inline_392 : inline_392 = combine (6, 8) [placed 4 (7, 5) card_184, placed 4 (7, 5) card_423, inline_390, placed 1 (0, 5) card_572, inline_391] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_392 : Valid inline_392 := by
  rw [eq_inline_392]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_184
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_423
  rcases hc with rfl | hc
  · exact valid_inline_390
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 5) valid_572
  subst c
  exact valid_inline_391

theorem eq_card_583 : card_583 = combine (7, 6) [placed 0 (3, 2) card_401, placed 2 (0, 12) card_552, placed 0 (3, 2) card_556, placed 0 (3, 2) card_575, inline_389, placed 2 (5, 10) card_579, inline_392, placed 1 (0, 4) card_582] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_583 : Valid card_583 := by
  rw [eq_card_583]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_401
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 12) valid_552
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_556
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_575
  rcases hc with rfl | hc
  · exact valid_inline_389
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 10) valid_579
  rcases hc with rfl | hc
  · exact valid_inline_392
  subst c
  exact placed_valid 1 (0, 4) valid_582

theorem eq_inline_393 : inline_393 = combine (4, 1) [placed 4 (4, 1) card_4, placed 0 (1, 0) card_121] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_393 : Valid inline_393 := by
  rw [eq_inline_393]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_4
  subst c
  exact placed_valid 0 (1, 0) valid_121

theorem eq_inline_394 : inline_394 = combine (1, 2) [placed 4 (4, 1) card_0, placed 0 (0, 0) card_203] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_394 : Valid inline_394 := by
  rw [eq_inline_394]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_203

theorem eq_inline_395 : inline_395 = combine (3, 4) [placed 0 (2, 0) card_39, inline_393, inline_394] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_395 : Valid inline_395 := by
  rw [eq_inline_395]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_39
  rcases hc with rfl | hc
  · exact valid_inline_393
  subst c
  exact valid_inline_394

theorem eq_card_584 : card_584 = combine (2, 1) [placed 0 (0, 1) card_5, inline_395] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_584 : Valid card_584 := by
  rw [eq_card_584]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_395

theorem eq_inline_396 : inline_396 = combine (1, 4) [placed 0 (1, 0) card_11, placed 1 (0, 1) card_358] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_396 : Valid inline_396 := by
  rw [eq_inline_396]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_11
  subst c
  exact placed_valid 1 (0, 1) valid_358

theorem eq_inline_397 : inline_397 = combine (4, 1) [placed 2 (1, 2) card_5, inline_396] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_397 : Valid inline_397 := by
  rw [eq_inline_397]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 2) valid_5
  subst c
  exact valid_inline_396

theorem eq_inline_398 : inline_398 = combine (1, 1) [placed 6 (4, 2) card_5, inline_397] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_398 : Valid inline_398 := by
  rw [eq_inline_398]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_5
  subst c
  exact valid_inline_397

theorem eq_card_585 : card_585 = combine (1, 3) [placed 4 (4, 2) card_5, inline_398] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_585 : Valid card_585 := by
  rw [eq_card_585]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_5
  subst c
  exact valid_inline_398

theorem eq_card_586 : card_586 = combine (4, 2) [placed 0 (1, 1) card_8, placed 0 (0, 0) card_179, placed 0 (0, 0) card_585] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_586 : Valid card_586 := by
  rw [eq_card_586]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_179
  subst c
  exact placed_valid 0 (0, 0) valid_585

theorem eq_card_587 : card_587 = combine (2, 5) [placed 0 (1, 1) card_12, placed 4 (3, 1) card_12, placed 2 (1, 7) card_12, placed 6 (3, 7) card_12, placed 1 (0, 2) card_586, placed 5 (0, 6) card_586] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_587 : Valid card_587 := by
  rw [eq_card_587]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 1) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 7) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_586
  subst c
  exact placed_valid 5 (0, 6) valid_586

theorem eq_card_588 : card_588 = combine (4, 3) [placed 1 (0, 2) card_42, placed 5 (0, 3) card_289, placed 0 (1, 0) card_291, placed 1 (2, 0) card_586] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_588 : Valid card_588 := by
  rw [eq_card_588]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_42
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_289
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_291
  subst c
  exact placed_valid 1 (2, 0) valid_586

theorem eq_card_589 : card_589 = combine (4, 2) [placed 1 (0, 2) card_7, placed 0 (1, 1) card_8, placed 5 (0, 3) card_9, placed 4 (5, 0) card_585] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_589 : Valid card_589 := by
  rw [eq_card_589]
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
  exact placed_valid 4 (5, 0) valid_585

theorem eq_card_590 : card_590 = combine (2, 3) [placed 0 (1, 0) card_52, placed 0 (0, 0) card_588] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_590 : Valid card_590 := by
  rw [eq_card_590]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_52
  subst c
  exact placed_valid 0 (0, 0) valid_588

theorem eq_inline_399 : inline_399 = combine (3, 6) [placed 6 (4, 6) card_5, placed 1 (1, 5) card_265] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_399 : Valid inline_399 := by
  rw [eq_inline_399]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_5
  subst c
  exact placed_valid 1 (1, 5) valid_265

theorem eq_inline_400 : inline_400 = combine (4, 4) [placed 2 (3, 8) card_12, placed 2 (3, 8) card_13, placed 2 (3, 8) card_14, placed 5 (0, 6) card_289, placed 5 (1, 7) card_435] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_400 : Valid inline_400 := by
  rw [eq_inline_400]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_289
  subst c
  exact placed_valid 5 (1, 7) valid_435

theorem eq_inline_401 : inline_401 = combine (3, 5) [placed 2 (3, 6) card_17, placed 7 (5, 6) card_80] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_401 : Valid inline_401 := by
  rw [eq_inline_401]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_17
  subst c
  exact placed_valid 7 (5, 6) valid_80

theorem eq_inline_402 : inline_402 = combine (4, 3) [placed 2 (1, 6) card_109, placed 7 (5, 6) card_157, inline_401] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_402 : Valid inline_402 := by
  rw [eq_inline_402]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_109
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_157
  subst c
  exact valid_inline_401

theorem eq_inline_403 : inline_403 = combine (4, 3) [placed 5 (3, 6) card_8, placed 4 (5, 2) card_19, placed 2 (1, 6) card_271] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_403 : Valid inline_403 := by
  rw [eq_inline_403]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_19
  subst c
  exact placed_valid 2 (1, 6) valid_271

theorem eq_inline_404 : inline_404 = combine (4, 4) [placed 0 (3, 2) card_13, placed 0 (1, 2) card_356, inline_402, placed 1 (2, 3) card_586, inline_403] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_404 : Valid inline_404 := by
  rw [eq_inline_404]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_356
  rcases hc with rfl | hc
  · exact valid_inline_402
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_586
  subst c
  exact valid_inline_403

theorem eq_card_591 : card_591 = combine (4, 6) [placed 1 (0, 5) card_42, placed 0 (1, 2) card_430, inline_399, inline_400, inline_404] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_591 : Valid card_591 := by
  rw [eq_card_591]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 5) valid_42
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_430
  rcases hc with rfl | hc
  · exact valid_inline_399
  rcases hc with rfl | hc
  · exact valid_inline_400
  subst c
  exact valid_inline_404

theorem eq_inline_405 : inline_405 = combine (1, 5) [placed 1 (0, 1) card_1, placed 2 (1, 6) card_158] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_405 : Valid inline_405 := by
  rw [eq_inline_405]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_1
  subst c
  exact placed_valid 2 (1, 6) valid_158

theorem eq_card_592 : card_592 = combine (1, 4) [placed 2 (0, 5) card_22, placed 6 (1, 4) card_36, placed 0 (0, 0) card_150, inline_405] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_592 : Valid card_592 := by
  rw [eq_card_592]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 4) valid_36
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_150
  subst c
  exact valid_inline_405

theorem eq_inline_406 : inline_406 = combine (4, 5) [placed 0 (3, 2) card_36, placed 0 (3, 1) card_105, placed 2 (3, 6) card_250, placed 2 (3, 6) card_592] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_406 : Valid inline_406 := by
  rw [eq_inline_406]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_36
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_105
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_250
  subst c
  exact placed_valid 2 (3, 6) valid_592

theorem eq_card_593 : card_593 = combine (4, 3) [placed 0 (0, 2) card_2, inline_406] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_593 : Valid card_593 := by
  rw [eq_card_593]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_2
  subst c
  exact valid_inline_406

theorem eq_inline_407 : inline_407 = combine (5, 5) [placed 3 (5, 3) card_5, placed 0 (4, 3) card_91] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_407 : Valid inline_407 := by
  rw [eq_inline_407]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_5
  subst c
  exact placed_valid 0 (4, 3) valid_91

theorem eq_inline_408 : inline_408 = combine (5, 2) [placed 1 (5, 1) card_5, placed 2 (5, 5) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_408 : Valid inline_408 := by
  rw [eq_inline_408]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 1) valid_5
  subst c
  exact placed_valid 2 (5, 5) valid_6

theorem eq_inline_409 : inline_409 = combine (5, 5) [placed 3 (5, 3) card_5, inline_408] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_409 : Valid inline_409 := by
  rw [eq_inline_409]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_5
  subst c
  exact valid_inline_408

theorem eq_inline_410 : inline_410 = combine (5, 1) [placed 5 (1, 5) card_375, inline_409] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_410 : Valid inline_410 := by
  rw [eq_inline_410]
  apply combination_rule (5, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_375
  subst c
  exact valid_inline_409

theorem eq_inline_411 : inline_411 = combine (1, 2) [placed 7 (2, 6) card_4, inline_410] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_411 : Valid inline_411 := by
  rw [eq_inline_411]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 6) valid_4
  subst c
  exact valid_inline_410

theorem eq_inline_412 : inline_412 = combine (2, 5) [placed 6 (2, 7) card_7, placed 1 (1, 3) card_208, inline_411] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_412 : Valid inline_412 := by
  rw [eq_inline_412]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 7) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_208
  subst c
  exact valid_inline_411

theorem eq_inline_413 : inline_413 = combine (2, 3) [placed 0 (2, 3) card_1, inline_412] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_413 : Valid inline_413 := by
  rw [eq_inline_413]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_1
  subst c
  exact valid_inline_412

theorem eq_inline_414 : inline_414 = combine (2, 3) [placed 0 (2, 3) card_1, placed 0 (1, 1) card_268] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_414 : Valid inline_414 := by
  rw [eq_inline_414]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_1
  subst c
  exact placed_valid 0 (1, 1) valid_268

theorem eq_inline_415 : inline_415 = combine (2, 6) [placed 3 (6, 3) card_272, placed 7 (6, 7) card_290, inline_413, inline_414, placed 3 (7, 3) card_593] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_415 : Valid inline_415 := by
  rw [eq_inline_415]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_272
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 7) valid_290
  rcases hc with rfl | hc
  · exact valid_inline_413
  rcases hc with rfl | hc
  · exact valid_inline_414
  subst c
  exact placed_valid 3 (7, 3) valid_593

theorem eq_card_594 : card_594 = combine (6, 4) [placed 7 (8, 4) card_53, inline_407, inline_415] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_594 : Valid card_594 := by
  rw [eq_card_594]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 4) valid_53
  rcases hc with rfl | hc
  · exact valid_inline_407
  subst c
  exact valid_inline_415

theorem eq_inline_416 : inline_416 = combine (4, 1) [placed 2 (1, 1) card_4, placed 2 (2, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_416 : Valid inline_416 := by
  rw [eq_inline_416]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 1) valid_4
  subst c
  exact placed_valid 2 (2, 1) valid_5

theorem eq_inline_417 : inline_417 = combine (5, 0) [placed 7 (6, 4) card_3, inline_416] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_417 : Valid inline_417 := by
  rw [eq_inline_417]
  apply combination_rule (5, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_3
  subst c
  exact valid_inline_416

theorem eq_inline_418 : inline_418 = combine (5, 1) [placed 7 (6, 5) card_4, inline_417] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_418 : Valid inline_418 := by
  rw [eq_inline_418]
  apply combination_rule (5, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_4
  subst c
  exact valid_inline_417

theorem eq_inline_419 : inline_419 = combine (2, 1) [placed 0 (0, 1) card_5, inline_418] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_419 : Valid inline_419 := by
  rw [eq_inline_419]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_418

theorem eq_inline_420 : inline_420 = combine (4, 2) [placed 0 (0, 1) card_2, placed 7 (7, 5) card_208] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_420 : Valid inline_420 := by
  rw [eq_inline_420]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_2
  subst c
  exact placed_valid 7 (7, 5) valid_208

theorem eq_inline_421 : inline_421 = combine (4, 2) [placed 6 (6, 2) card_5, placed 1 (3, 1) card_153] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_421 : Valid inline_421 := by
  rw [eq_inline_421]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 2) valid_5
  subst c
  exact placed_valid 1 (3, 1) valid_153

theorem eq_inline_422 : inline_422 = combine (5, 2) [placed 7 (6, 5) card_5, inline_421] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_422 : Valid inline_422 := by
  rw [eq_inline_422]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_5
  subst c
  exact valid_inline_421

theorem eq_inline_423 : inline_423 = combine (4, 2) [placed 0 (0, 1) card_2, placed 7 (7, 5) card_157] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_423 : Valid inline_423 := by
  rw [eq_inline_423]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_2
  subst c
  exact placed_valid 7 (7, 5) valid_157

theorem eq_inline_424 : inline_424 = combine (6, 2) [placed 7 (7, 5) card_8, inline_419, inline_420, inline_422, inline_423] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_424 : Valid inline_424 := by
  rw [eq_inline_424]
  apply combination_rule (6, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 5) valid_8
  rcases hc with rfl | hc
  · exact valid_inline_419
  rcases hc with rfl | hc
  · exact valid_inline_420
  rcases hc with rfl | hc
  · exact valid_inline_422
  subst c
  exact valid_inline_423

theorem eq_inline_425 : inline_425 = combine (6, 3) [placed 2 (3, 4) card_5, inline_424] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_425 : Valid inline_425 := by
  rw [eq_inline_425]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 4) valid_5
  subst c
  exact valid_inline_424

theorem eq_inline_426 : inline_426 = combine (6, 4) [placed 0 (3, 4) card_5, inline_425] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_426 : Valid inline_426 := by
  rw [eq_inline_426]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_5
  subst c
  exact valid_inline_425

theorem eq_card_595 : card_595 = combine (6, 5) [placed 0 (2, 4) card_4, inline_426] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_595 : Valid card_595 := by
  rw [eq_card_595]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_4
  subst c
  exact valid_inline_426

theorem eq_inline_427 : inline_427 = combine (4, 5) [placed 7 (4, 5) card_2, placed 0 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_427 : Valid inline_427 := by
  rw [eq_inline_427]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_2
  subst c
  exact placed_valid 0 (1, 4) valid_5

theorem eq_inline_428 : inline_428 = combine (4, 2) [placed 0 (0, 1) card_2, inline_427] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_428 : Valid inline_428 := by
  rw [eq_inline_428]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_2
  subst c
  exact valid_inline_427

theorem eq_inline_429 : inline_429 = combine (4, 3) [placed 7 (4, 5) card_0, placed 2 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_429 : Valid inline_429 := by
  rw [eq_inline_429]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_0
  subst c
  exact placed_valid 2 (1, 4) valid_5

theorem eq_inline_430 : inline_430 = combine (4, 2) [placed 0 (0, 1) card_2, inline_429] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_430 : Valid inline_430 := by
  rw [eq_inline_430]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_2
  subst c
  exact valid_inline_429

theorem eq_inline_431 : inline_431 = combine (4, 2) [placed 0 (0, 1) card_2, placed 1 (2, 1) card_82] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_431 : Valid inline_431 := by
  rw [eq_inline_431]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_2
  subst c
  exact placed_valid 1 (2, 1) valid_82

theorem eq_inline_432 : inline_432 = combine (5, 4) [placed 5 (1, 4) card_6, placed 0 (0, 0) card_595, inline_431] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_432 : Valid inline_432 := by
  rw [eq_inline_432]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_595
  subst c
  exact valid_inline_431

theorem eq_card_596 : card_596 = combine (4, 4) [placed 2 (1, 5) card_197, inline_428, inline_430, inline_432] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_596 : Valid card_596 := by
  rw [eq_card_596]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_197
  rcases hc with rfl | hc
  · exact valid_inline_428
  rcases hc with rfl | hc
  · exact valid_inline_430
  subst c
  exact valid_inline_432

theorem eq_inline_433 : inline_433 = combine (5, 4) [placed 6 (6, 7) card_13, placed 0 (2, 2) card_109, placed 0 (2, 2) card_291] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_433 : Valid inline_433 := by
  rw [eq_inline_433]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_109
  subst c
  exact placed_valid 0 (2, 2) valid_291

theorem eq_inline_434 : inline_434 = combine (4, 2) [placed 7 (5, 5) card_5, placed 4 (5, 2) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_434 : Valid inline_434 := by
  rw [eq_inline_434]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 5) valid_5
  subst c
  exact placed_valid 4 (5, 2) valid_5

theorem eq_inline_435 : inline_435 = combine (5, 2) [placed 2 (5, 6) card_7, inline_434] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_435 : Valid inline_435 := by
  rw [eq_inline_435]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 6) valid_7
  subst c
  exact valid_inline_434

theorem eq_inline_436 : inline_436 = combine (6, 1) [placed 2 (2, 2) card_4, placed 5 (5, 5) card_4] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_436 : Valid inline_436 := by
  rw [eq_inline_436]
  apply combination_rule (6, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 2) valid_4
  subst c
  exact placed_valid 5 (5, 5) valid_4

theorem eq_inline_437 : inline_437 = combine (5, 2) [placed 4 (5, 2) card_5, inline_436] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_437 : Valid inline_437 := by
  rw [eq_inline_437]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_5
  subst c
  exact valid_inline_436

theorem eq_inline_438 : inline_438 = combine (4, 2) [placed 6 (5, 6) card_140, inline_437] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_438 : Valid inline_438 := by
  rw [eq_inline_438]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_140
  subst c
  exact valid_inline_437

theorem eq_inline_439 : inline_439 = combine (5, 4) [inline_435, inline_438, placed 1 (1, 2) card_596] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_439 : Valid inline_439 := by
  rw [eq_inline_439]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_435
  rcases hc with rfl | hc
  · exact valid_inline_438
  subst c
  exact placed_valid 1 (1, 2) valid_596

theorem eq_card_597 : card_597 = combine (5, 5) [placed 1 (1, 2) card_272, placed 5 (1, 6) card_290, placed 1 (0, 2) card_593, inline_433, inline_439] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_597 : Valid card_597 := by
  rw [eq_card_597]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_272
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_290
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_593
  rcases hc with rfl | hc
  · exact valid_inline_433
  subst c
  exact valid_inline_439

theorem eq_inline_440 : inline_440 = combine (5, 5) [placed 4 (6, 5) card_5, placed 4 (7, 3) card_133] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_440 : Valid inline_440 := by
  rw [eq_inline_440]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 5) valid_5
  subst c
  exact placed_valid 4 (7, 3) valid_133

theorem eq_inline_441 : inline_441 = combine (4, 5) [placed 5 (3, 8) card_0, inline_440] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_441 : Valid inline_441 := by
  rw [eq_inline_441]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_0
  subst c
  exact valid_inline_440

theorem eq_inline_442 : inline_442 = combine (3, 6) [placed 1 (3, 4) card_5, inline_441] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_442 : Valid inline_442 := by
  rw [eq_inline_442]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_5
  subst c
  exact valid_inline_441

theorem eq_inline_443 : inline_443 = combine (5, 5) [placed 4 (6, 5) card_5, placed 6 (7, 7) card_133] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_443 : Valid inline_443 := by
  rw [eq_inline_443]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 5) valid_5
  subst c
  exact placed_valid 6 (7, 7) valid_133

theorem eq_inline_444 : inline_444 = combine (4, 5) [placed 5 (3, 8) card_0, inline_443] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_444 : Valid inline_444 := by
  rw [eq_inline_444]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_0
  subst c
  exact valid_inline_443

theorem eq_inline_445 : inline_445 = combine (3, 6) [placed 1 (3, 4) card_5, inline_444] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_445 : Valid inline_445 := by
  rw [eq_inline_445]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_5
  subst c
  exact valid_inline_444

theorem eq_inline_446 : inline_446 = combine (5, 5) [placed 4 (6, 5) card_5, placed 5 (2, 6) card_413] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_446 : Valid inline_446 := by
  rw [eq_inline_446]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 5) valid_5
  subst c
  exact placed_valid 5 (2, 6) valid_413

theorem eq_inline_447 : inline_447 = combine (4, 5) [placed 5 (3, 8) card_0, inline_446] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_447 : Valid inline_447 := by
  rw [eq_inline_447]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_0
  subst c
  exact valid_inline_446

theorem eq_inline_448 : inline_448 = combine (3, 6) [placed 1 (3, 4) card_5, inline_447] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_448 : Valid inline_448 := by
  rw [eq_inline_448]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_5
  subst c
  exact valid_inline_447

theorem eq_card_598 : card_598 = combine (3, 5) [inline_442, inline_445, placed 1 (2, 4) card_584, placed 2 (2, 10) card_591, placed 4 (8, 1) card_594, inline_448, placed 0 (1, 2) card_597] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_598 : Valid card_598 := by
  rw [eq_card_598]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_442
  rcases hc with rfl | hc
  · exact valid_inline_445
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_584
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 10) valid_591
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 1) valid_594
  rcases hc with rfl | hc
  · exact valid_inline_448
  subst c
  exact placed_valid 0 (1, 2) valid_597

theorem eq_inline_449 : inline_449 = combine (5, 6) [placed 0 (2, 5) card_5, placed 0 (4, 2) card_64] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_449 : Valid inline_449 := by
  rw [eq_inline_449]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_5
  subst c
  exact placed_valid 0 (4, 2) valid_64

theorem eq_inline_450 : inline_450 = combine (4, 4) [placed 6 (7, 5) card_0, placed 0 (4, 2) card_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_450 : Valid inline_450 := by
  rw [eq_inline_450]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 5) valid_0
  subst c
  exact placed_valid 0 (4, 2) valid_44

theorem eq_inline_451 : inline_451 = combine (6, 5) [placed 5 (2, 5) card_6, placed 5 (3, 5) card_16, inline_450] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_451 : Valid inline_451 := by
  rw [eq_inline_451]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_16
  subst c
  exact valid_inline_450

theorem eq_inline_452 : inline_452 = combine (5, 5) [placed 0 (2, 4) card_8, placed 1 (2, 4) card_17, placed 1 (2, 4) card_41, inline_449, inline_451] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_452 : Valid inline_452 := by
  rw [eq_inline_452]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_41
  rcases hc with rfl | hc
  · exact valid_inline_449
  subst c
  exact valid_inline_451

theorem eq_inline_453 : inline_453 = combine (2, 5) [placed 3 (3, 2) card_5, inline_452] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_453 : Valid inline_453 := by
  rw [eq_inline_453]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 2) valid_5
  subst c
  exact valid_inline_452

theorem eq_inline_454 : inline_454 = combine (4, 5) [placed 1 (3, 2) card_5, inline_453] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_454 : Valid inline_454 := by
  rw [eq_inline_454]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 2) valid_5
  subst c
  exact valid_inline_453

theorem eq_inline_455 : inline_455 = combine (3, 2) [placed 6 (4, 6) card_9, placed 7 (4, 5) card_251, inline_454] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_455 : Valid inline_455 := by
  rw [eq_inline_455]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_251
  subst c
  exact valid_inline_454

theorem eq_inline_456 : inline_456 = combine (3, 5) [placed 4 (4, 2) card_10, placed 0 (3, 2) card_27, placed 4 (4, 2) card_48, placed 4 (4, 2) card_63, inline_455] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_456 : Valid inline_456 := by
  rw [eq_inline_456]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_48
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_63
  subst c
  exact valid_inline_455

theorem eq_inline_457 : inline_457 = combine (3, 4) [placed 2 (0, 4) card_2, inline_456] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_457 : Valid inline_457 := by
  rw [eq_inline_457]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 4) valid_2
  subst c
  exact valid_inline_456

theorem eq_card_599 : card_599 = combine (4, 3) [placed 5 (0, 4) card_107, placed 5 (0, 4) card_163, placed 2 (0, 7) card_401, inline_457] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_599 : Valid card_599 := by
  rw [eq_card_599]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_107
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_163
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_401
  subst c
  exact valid_inline_457

theorem eq_inline_458 : inline_458 = combine (3, 5) [placed 0 (2, 2) card_20, placed 5 (0, 5) card_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_458 : Valid inline_458 := by
  rw [eq_inline_458]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_20
  subst c
  exact placed_valid 5 (0, 5) valid_55

theorem eq_card_600 : card_600 = combine (3, 2) [placed 6 (3, 5) card_23, inline_458] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_600 : Valid card_600 := by
  rw [eq_card_600]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 5) valid_23
  subst c
  exact valid_inline_458

theorem eq_inline_459 : inline_459 = combine (3, 5) [placed 0 (3, 2) card_29, placed 7 (4, 5) card_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_459 : Valid inline_459 := by
  rw [eq_inline_459]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_29
  subst c
  exact placed_valid 7 (4, 5) valid_35

theorem eq_inline_460 : inline_460 = combine (4, 4) [inline_459, placed 1 (1, 2) card_499, placed 0 (0, 1) card_501] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_460 : Valid inline_460 := by
  rw [eq_inline_460]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_459
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_499
  subst c
  exact placed_valid 0 (0, 1) valid_501

theorem eq_inline_461 : inline_461 = combine (5, 2) [placed 0 (3, 1) card_66, placed 1 (3, 2) card_94] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_461 : Valid inline_461 := by
  rw [eq_inline_461]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_66
  subst c
  exact placed_valid 1 (3, 2) valid_94

theorem eq_inline_462 : inline_462 = combine (4, 2) [placed 2 (3, 5) card_15, inline_461] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_462 : Valid inline_462 := by
  rw [eq_inline_462]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_15
  subst c
  exact valid_inline_461

theorem eq_inline_463 : inline_463 = combine (6, 3) [placed 4 (6, 3) card_1, inline_462] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_463 : Valid inline_463 := by
  rw [eq_inline_463]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_1
  subst c
  exact valid_inline_462

theorem eq_inline_464 : inline_464 = combine (2, 4) [placed 4 (4, 4) card_3, inline_463] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_464 : Valid inline_464 := by
  rw [eq_inline_464]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 4) valid_3
  subst c
  exact valid_inline_463

theorem eq_inline_465 : inline_465 = combine (2, 4) [placed 4 (4, 4) card_3, placed 0 (2, 2) card_72] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_465 : Valid inline_465 := by
  rw [eq_inline_465]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 4) valid_3
  subst c
  exact placed_valid 0 (2, 2) valid_72

theorem eq_inline_466 : inline_466 = combine (4, 4) [placed 2 (3, 6) card_406, placed 1 (1, 2) card_499, inline_464, placed 2 (1, 7) card_600, inline_465] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_466 : Valid inline_466 := by
  rw [eq_inline_466]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_406
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_499
  rcases hc with rfl | hc
  · exact valid_inline_464
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_600
  subst c
  exact valid_inline_465

theorem eq_inline_467 : inline_467 = combine (4, 4) [placed 2 (3, 6) card_406, placed 0 (0, 1) card_501] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_467 : Valid inline_467 := by
  rw [eq_inline_467]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_406
  subst c
  exact placed_valid 0 (0, 1) valid_501

theorem eq_card_601 : card_601 = combine (4, 3) [placed 0 (0, 1) card_247, inline_460, inline_466, inline_467] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_601 : Valid card_601 := by
  rw [eq_card_601]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_247
  rcases hc with rfl | hc
  · exact valid_inline_460
  rcases hc with rfl | hc
  · exact valid_inline_466
  subst c
  exact valid_inline_467

theorem eq_inline_468 : inline_468 = combine (5, 8) [placed 0 (3, 4) card_320, placed 5 (2, 8) card_496] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_468 : Valid inline_468 := by
  rw [eq_inline_468]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_320
  subst c
  exact placed_valid 5 (2, 8) valid_496

theorem eq_inline_469 : inline_469 = combine (6, 8) [placed 2 (3, 11) card_59, placed 5 (2, 8) card_497, inline_468, placed 0 (3, 3) card_555] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_469 : Valid inline_469 := by
  rw [eq_inline_469]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 11) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_497
  rcases hc with rfl | hc
  · exact valid_inline_468
  subst c
  exact placed_valid 0 (3, 3) valid_555

theorem eq_inline_470 : inline_470 = combine (6, 8) [placed 2 (3, 8) card_2, placed 2 (5, 12) card_545] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_470 : Valid inline_470 := by
  rw [eq_inline_470]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_2
  subst c
  exact placed_valid 2 (5, 12) valid_545

theorem eq_inline_471 : inline_471 = combine (7, 7) [placed 5 (3, 8) card_107, placed 5 (3, 8) card_163, placed 2 (3, 11) card_556, inline_470] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_471 : Valid inline_471 := by
  rw [eq_inline_471]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_107
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_163
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 11) valid_556
  subst c
  exact valid_inline_470

theorem eq_inline_472 : inline_472 = combine (6, 5) [placed 0 (3, 4) card_157, placed 4 (6, 3) card_383] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_472 : Valid inline_472 := by
  rw [eq_inline_472]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_157
  subst c
  exact placed_valid 4 (6, 3) valid_383

theorem eq_inline_473 : inline_473 = combine (6, 6) [placed 0 (5, 5) card_18, placed 7 (7, 8) card_381] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_473 : Valid inline_473 := by
  rw [eq_inline_473]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 5) valid_18
  subst c
  exact placed_valid 7 (7, 8) valid_381

theorem eq_inline_474 : inline_474 = combine (5, 7) [placed 0 (5, 4) card_64, placed 5 (2, 8) card_500] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_474 : Valid inline_474 := by
  rw [eq_inline_474]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 4) valid_64
  subst c
  exact placed_valid 5 (2, 8) valid_500

theorem eq_inline_475 : inline_475 = combine (5, 5) [inline_472, inline_473, inline_474, placed 5 (1, 8) card_601] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_475 : Valid inline_475 := by
  rw [eq_inline_475]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_472
  rcases hc with rfl | hc
  · exact valid_inline_473
  rcases hc with rfl | hc
  · exact valid_inline_474
  subst c
  exact placed_valid 5 (1, 8) valid_601

theorem eq_inline_476 : inline_476 = combine (6, 8) [placed 0 (3, 5) card_119, placed 5 (2, 8) card_497, placed 1 (2, 4) card_498, inline_475] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_476 : Valid inline_476 := by
  rw [eq_inline_476]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 5) valid_119
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_497
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_498
  subst c
  exact valid_inline_475

theorem eq_card_602 : card_602 = combine (6, 7) [placed 0 (0, 1) card_553, inline_469, inline_471, placed 0 (2, 2) card_557, placed 1 (2, 4) card_564, placed 1 (2, 4) card_568, placed 5 (0, 8) card_573, placed 2 (2, 10) card_574, placed 2 (0, 13) card_583, placed 2 (0, 12) card_598, placed 0 (3, 4) card_599, inline_476] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_602 : Valid card_602 := by
  rw [eq_card_602]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_553
  rcases hc with rfl | hc
  · exact valid_inline_469
  rcases hc with rfl | hc
  · exact valid_inline_471
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_557
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_564
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_568
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 8) valid_573
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 10) valid_574
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 13) valid_583
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 12) valid_598
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_599
  subst c
  exact valid_inline_476

theorem eq_inline_477 : inline_477 = combine (1, 2) [placed 2 (1, 6) card_7, placed 5 (0, 5) card_8, placed 6 (2, 6) card_9, placed 2 (0, 6) card_427] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_477 : Valid inline_477 := by
  rw [eq_inline_477]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_9
  subst c
  exact placed_valid 2 (0, 6) valid_427

theorem eq_card_603 : card_603 = combine (1, 5) [placed 4 (2, 1) card_13, placed 6 (2, 7) card_14, placed 2 (0, 7) card_31, placed 4 (2, 1) card_189, placed 2 (0, 7) card_367, placed 0 (0, 2) card_457, inline_477] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_603 : Valid card_603 := by
  rw [eq_card_603]
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
  · exact placed_valid 0 (0, 2) valid_457
  subst c
  exact valid_inline_477

theorem eq_inline_478 : inline_478 = combine (3, 4) [placed 0 (0, 3) card_5, placed 0 (1, 0) card_267] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_478 : Valid inline_478 := by
  rw [eq_inline_478]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_267

theorem eq_card_604 : card_604 = combine (3, 2) [placed 2 (0, 3) card_5, inline_478] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_604 : Valid card_604 := by
  rw [eq_card_604]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_5
  subst c
  exact valid_inline_478

theorem eq_inline_479 : inline_479 = combine (1, 3) [placed 4 (4, 0) card_115, placed 0 (0, 1) card_585, placed 0 (1, 0) card_604] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_479 : Valid inline_479 := by
  rw [eq_inline_479]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_585
  subst c
  exact placed_valid 0 (1, 0) valid_604

theorem eq_card_605 : card_605 = combine (4, 3) [placed 1 (0, 2) card_12, placed 1 (0, 1) card_135, placed 5 (0, 5) card_182, placed 0 (1, 1) card_474, inline_479] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_605 : Valid card_605 := by
  rw [eq_card_605]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_135
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_182
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_474
  subst c
  exact valid_inline_479

theorem eq_inline_480 : inline_480 = combine (3, 4) [placed 2 (3, 6) card_53, placed 4 (4, 1) card_240] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_480 : Valid inline_480 := by
  rw [eq_inline_480]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_53
  subst c
  exact placed_valid 4 (4, 1) valid_240

theorem eq_card_606 : card_606 = combine (3, 3) [placed 1 (0, 2) card_28, placed 0 (0, 1) card_168, inline_480] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_606 : Valid card_606 := by
  rw [eq_card_606]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_168
  subst c
  exact valid_inline_480

theorem eq_inline_481 : inline_481 = combine (4, 2) [placed 5 (3, 5) card_8, placed 3 (6, 2) card_383] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_481 : Valid inline_481 := by
  rw [eq_inline_481]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_8
  subst c
  exact placed_valid 3 (6, 2) valid_383

theorem eq_inline_482 : inline_482 = combine (2, 5) [placed 3 (5, 3) card_25, placed 6 (2, 6) card_42] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_482 : Valid inline_482 := by
  rw [eq_inline_482]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_25
  subst c
  exact placed_valid 6 (2, 6) valid_42

theorem eq_inline_483 : inline_483 = combine (1, 2) [placed 7 (5, 6) card_352, inline_482] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_483 : Valid inline_483 := by
  rw [eq_inline_483]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_352
  subst c
  exact valid_inline_482

theorem eq_inline_484 : inline_484 = combine (4, 6) [placed 6 (4, 7) card_7, placed 3 (5, 3) card_8, inline_483] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_484 : Valid inline_484 := by
  rw [eq_inline_484]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_8
  subst c
  exact valid_inline_483

theorem eq_inline_485 : inline_485 = combine (4, 6) [placed 3 (5, 3) card_197, placed 0 (1, 2) card_363, placed 3 (5, 3) card_371, placed 4 (5, 2) card_606] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_485 : Valid inline_485 := by
  rw [eq_inline_485]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_363
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_371
  subst c
  exact placed_valid 4 (5, 2) valid_606

theorem eq_card_607 : card_607 = combine (4, 3) [placed 6 (5, 7) card_13, placed 2 (1, 7) card_211, inline_481, inline_484, inline_485] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_607 : Valid card_607 := by
  rw [eq_card_607]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_211
  rcases hc with rfl | hc
  · exact valid_inline_481
  rcases hc with rfl | hc
  · exact valid_inline_484
  subst c
  exact valid_inline_485

theorem eq_inline_486 : inline_486 = combine (5, 3) [placed 4 (5, 3) card_18, placed 7 (5, 6) card_375] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_486 : Valid inline_486 := by
  rw [eq_inline_486]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_18
  subst c
  exact placed_valid 7 (5, 6) valid_375

theorem eq_inline_487 : inline_487 = combine (2, 5) [placed 7 (5, 6) card_28, placed 6 (2, 6) card_42] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_487 : Valid inline_487 := by
  rw [eq_inline_487]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_28
  subst c
  exact placed_valid 6 (2, 6) valid_42

theorem eq_inline_488 : inline_488 = combine (2, 5) [placed 6 (2, 6) card_42, placed 0 (1, 3) card_58] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_488 : Valid inline_488 := by
  rw [eq_inline_488]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_42
  subst c
  exact placed_valid 0 (1, 3) valid_58

theorem eq_inline_489 : inline_489 = combine (1, 2) [inline_486, inline_487, inline_488] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_489 : Valid inline_489 := by
  rw [eq_inline_489]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_486
  rcases hc with rfl | hc
  · exact valid_inline_487
  subst c
  exact valid_inline_488

theorem eq_card_608 : card_608 = combine (4, 6) [placed 2 (3, 8) card_13, placed 2 (3, 8) card_31, placed 2 (1, 7) card_355, placed 0 (1, 2) card_364, placed 0 (0, 3) card_434, inline_489] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_608 : Valid card_608 := by
  rw [eq_card_608]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_355
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_364
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_434
  subst c
  exact valid_inline_489

theorem eq_inline_490 : inline_490 = combine (2, 1) [placed 5 (1, 4) card_5, placed 5 (0, 2) card_48] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_490 : Valid inline_490 := by
  rw [eq_inline_490]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 5 (0, 2) valid_48

theorem eq_inline_491 : inline_491 = combine (3, 3) [placed 1 (0, 1) card_25, placed 0 (3, 0) card_54] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_491 : Valid inline_491 := by
  rw [eq_inline_491]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_25
  subst c
  exact placed_valid 0 (3, 0) valid_54

theorem eq_card_609 : card_609 = combine (3, 1) [inline_490, inline_491] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_609 : Valid card_609 := by
  rw [eq_card_609]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_490
  subst c
  exact valid_inline_491

theorem eq_card_610 : card_610 = combine (1, 5) [placed 0 (0, 1) card_19, placed 3 (2, 2) card_197, placed 0 (0, 1) card_225, placed 2 (0, 6) card_609] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_610 : Valid card_610 := by
  rw [eq_card_610]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 3 (2, 2) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_225
  subst c
  exact placed_valid 2 (0, 6) valid_609

theorem eq_inline_492 : inline_492 = combine (2, 3) [placed 2 (2, 7) card_7, placed 0 (1, 3) card_17, placed 5 (1, 6) card_93] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_492 : Valid inline_492 := by
  rw [eq_inline_492]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_17
  subst c
  exact placed_valid 5 (1, 6) valid_93

theorem eq_card_611 : card_611 = combine (2, 5) [placed 4 (2, 3) card_27, placed 5 (0, 7) card_47, inline_492] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_611 : Valid card_611 := by
  rw [eq_card_611]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 3) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_47
  subst c
  exact valid_inline_492

theorem eq_inline_493 : inline_493 = combine (1, 2) [placed 0 (1, 1) card_6, placed 4 (1, 1) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_493 : Valid inline_493 := by
  rw [eq_inline_493]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_6
  subst c
  exact placed_valid 4 (1, 1) valid_6

theorem eq_inline_494 : inline_494 = combine (0, 2) [placed 7 (1, 6) card_0, placed 1 (0, 1) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_494 : Valid inline_494 := by
  rw [eq_inline_494]
  apply combination_rule (0, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 6) valid_0
  subst c
  exact placed_valid 1 (0, 1) valid_3

theorem eq_inline_495 : inline_495 = combine (1, 2) [placed 7 (1, 5) card_4, placed 0 (1, 1) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_495 : Valid inline_495 := by
  rw [eq_inline_495]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_4
  subst c
  exact placed_valid 0 (1, 1) valid_6

theorem eq_inline_496 : inline_496 = combine (1, 5) [inline_493, inline_494, inline_495] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_496 : Valid inline_496 := by
  rw [eq_inline_496]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_493
  rcases hc with rfl | hc
  · exact valid_inline_494
  subst c
  exact valid_inline_495

theorem eq_card_612 : card_612 = combine (1, 4) [placed 6 (1, 4) card_36, placed 0 (0, 0) card_50, placed 0 (0, 0) card_54, inline_496] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_612 : Valid card_612 := by
  rw [eq_card_612]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 4) valid_36
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_54
  subst c
  exact valid_inline_496

theorem eq_card_613 : card_613 = combine (2, 5) [placed 0 (1, 0) card_104, placed 4 (2, 0) card_329, placed 2 (1, 8) card_409, placed 0 (1, 2) card_612, placed 2 (1, 6) card_612, placed 6 (2, 6) card_612] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_613 : Valid card_613 := by
  rw [eq_card_613]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_104
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 0) valid_329
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_409
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_612
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_612
  subst c
  exact placed_valid 6 (2, 6) valid_612

theorem eq_inline_497 : inline_497 = combine (2, 4) [placed 0 (0, 4) card_1, placed 2 (2, 6) card_425] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_497 : Valid inline_497 := by
  rw [eq_inline_497]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 4) valid_1
  subst c
  exact placed_valid 2 (2, 6) valid_425

theorem eq_inline_498 : inline_498 = combine (4, 3) [placed 5 (0, 4) card_68, placed 2 (3, 8) card_495] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_498 : Valid inline_498 := by
  rw [eq_inline_498]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_68
  subst c
  exact placed_valid 2 (3, 8) valid_495

theorem eq_inline_499 : inline_499 = combine (4, 4) [placed 2 (3, 6) card_66, placed 0 (3, 2) card_66] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_499 : Valid inline_499 := by
  rw [eq_inline_499]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_66
  subst c
  exact placed_valid 0 (3, 2) valid_66

theorem eq_inline_500 : inline_500 = combine (4, 3) [placed 5 (0, 4) card_68, inline_499] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_500 : Valid inline_500 := by
  rw [eq_inline_500]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_68
  subst c
  exact valid_inline_499

theorem eq_inline_501 : inline_501 = combine (4, 3) [placed 5 (0, 4) card_68, placed 2 (4, 6) card_612] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_501 : Valid inline_501 := by
  rw [eq_inline_501]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_68
  subst c
  exact placed_valid 2 (4, 6) valid_612

theorem eq_inline_502 : inline_502 = combine (5, 3) [placed 2 (3, 8) card_276, inline_497, placed 2 (3, 9) card_611, inline_498, inline_500, inline_501] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_502 : Valid inline_502 := by
  rw [eq_inline_502]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_276
  rcases hc with rfl | hc
  · exact valid_inline_497
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_611
  rcases hc with rfl | hc
  · exact valid_inline_498
  rcases hc with rfl | hc
  · exact valid_inline_500
  subst c
  exact valid_inline_501

theorem eq_card_614 : card_614 = combine (5, 5) [placed 1 (0, 4) card_68, placed 2 (3, 7) card_558, inline_502] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_614 : Valid card_614 := by
  rw [eq_card_614]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_68
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_558
  subst c
  exact valid_inline_502

theorem eq_inline_503 : inline_503 = combine (4, 3) [placed 2 (4, 7) card_11, placed 2 (3, 6) card_20, placed 0 (3, 2) card_402] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_503 : Valid inline_503 := by
  rw [eq_inline_503]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 7) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_20
  subst c
  exact placed_valid 0 (3, 2) valid_402

theorem eq_inline_504 : inline_504 = combine (4, 4) [placed 6 (7, 5) card_0, inline_503] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_504 : Valid inline_504 := by
  rw [eq_inline_504]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 5) valid_0
  subst c
  exact valid_inline_503

theorem eq_inline_505 : inline_505 = combine (6, 5) [placed 2 (3, 5) card_5, inline_504] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_505 : Valid inline_505 := by
  rw [eq_inline_505]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_5
  subst c
  exact valid_inline_504

theorem eq_inline_506 : inline_506 = combine (6, 4) [placed 5 (2, 5) card_139, placed 3 (6, 4) card_148, inline_505] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_506 : Valid inline_506 := by
  rw [eq_inline_506]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_139
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_148
  subst c
  exact valid_inline_505

theorem eq_inline_507 : inline_507 = combine (4, 6) [placed 0 (3, 3) card_43, placed 2 (2, 8) card_57, inline_506] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_507 : Valid inline_507 := by
  rw [eq_inline_507]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_43
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_57
  subst c
  exact valid_inline_506

theorem eq_inline_508 : inline_508 = combine (5, 5) [placed 4 (6, 2) card_116, placed 2 (2, 7) card_134, placed 2 (2, 7) card_180, placed 2 (2, 8) card_435, placed 2 (3, 7) card_558, placed 0 (2, 0) card_561, inline_507] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_508 : Valid inline_508 := by
  rw [eq_inline_508]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_558
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_561
  subst c
  exact valid_inline_507

theorem eq_card_615 : card_615 = combine (4, 5) [placed 0 (0, 1) card_362, placed 0 (0, 0) card_614, inline_508] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_615 : Valid card_615 := by
  rw [eq_card_615]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_362
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_614
  subst c
  exact valid_inline_508

theorem eq_inline_509 : inline_509 = combine (2, 6) [placed 0 (2, 2) card_6, placed 3 (3, 3) card_123] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_509 : Valid inline_509 := by
  rw [eq_inline_509]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_6
  subst c
  exact placed_valid 3 (3, 3) valid_123

theorem eq_inline_510 : inline_510 = combine (2, 5) [placed 0 (2, 1) card_11, inline_509, placed 0 (1, 1) card_521] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_510 : Valid inline_510 := by
  rw [eq_inline_510]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_11
  rcases hc with rfl | hc
  · exact valid_inline_509
  subst c
  exact placed_valid 0 (1, 1) valid_521

theorem eq_card_616 : card_616 = combine (3, 3) [placed 0 (0, 1) card_345, placed 1 (0, 2) card_421, placed 0 (0, 1) card_522, placed 0 (1, 0) card_530, placed 2 (0, 6) card_533, placed 0 (0, 0) card_534, inline_510] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_616 : Valid card_616 := by
  rw [eq_card_616]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_345
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_421
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_522
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_530
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_533
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_534
  subst c
  exact valid_inline_510

theorem eq_card_617 : card_617 = combine (4, 3) [placed 6 (5, 7) card_14, placed 2 (2, 6) card_136, placed 7 (7, 6) card_332, placed 0 (2, 1) card_616] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_617 : Valid card_617 := by
  rw [eq_card_617]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_136
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_332
  subst c
  exact placed_valid 0 (2, 1) valid_616

theorem eq_inline_511 : inline_511 = combine (3, 5) [placed 6 (3, 7) card_53, placed 1 (3, 3) card_378] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_511 : Valid inline_511 := by
  rw [eq_inline_511]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 7) valid_53
  subst c
  exact placed_valid 1 (3, 3) valid_378

theorem eq_inline_512 : inline_512 = combine (3, 4) [placed 7 (6, 6) card_25, inline_511] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_512 : Valid inline_512 := by
  rw [eq_inline_512]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_25
  subst c
  exact valid_inline_511

theorem eq_inline_513 : inline_513 = combine (5, 6) [placed 0 (5, 2) card_7, placed 1 (4, 3) card_8, placed 4 (6, 2) card_9, inline_512] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_513 : Valid inline_513 := by
  rw [eq_inline_513]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_9
  subst c
  exact valid_inline_512

theorem eq_inline_514 : inline_514 = combine (5, 6) [placed 0 (5, 2) card_7, placed 1 (4, 3) card_8, placed 4 (6, 2) card_9, placed 1 (2, 3) card_604] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_514 : Valid inline_514 := by
  rw [eq_inline_514]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_9
  subst c
  exact placed_valid 1 (2, 3) valid_604

theorem eq_inline_515 : inline_515 = combine (5, 6) [placed 4 (6, 2) card_9, placed 1 (2, 3) card_171, placed 5 (3, 7) card_577, placed 6 (6, 7) card_609] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_515 : Valid inline_515 := by
  rw [eq_inline_515]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_171
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_577
  subst c
  exact placed_valid 6 (6, 7) valid_609

theorem eq_inline_516 : inline_516 = combine (5, 6) [placed 4 (6, 2) card_9, placed 3 (8, 3) card_256, placed 5 (3, 7) card_577] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_516 : Valid inline_516 := by
  rw [eq_inline_516]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_256
  subst c
  exact placed_valid 5 (3, 7) valid_577

theorem eq_inline_517 : inline_517 = combine (6, 4) [placed 6 (6, 4) card_4, placed 1 (1, 4) card_113] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_517 : Valid inline_517 := by
  rw [eq_inline_517]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 4) valid_4
  subst c
  exact placed_valid 1 (1, 4) valid_113

theorem eq_inline_518 : inline_518 = combine (3, 4) [placed 0 (2, 4) card_5, inline_517] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_518 : Valid inline_518 := by
  rw [eq_inline_518]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_5
  subst c
  exact valid_inline_517

theorem eq_inline_519 : inline_519 = combine (4, 4) [placed 3 (6, 3) card_80, placed 1 (2, 2) card_111, placed 0 (3, 1) card_616, inline_518] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_519 : Valid inline_519 := by
  rw [eq_inline_519]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_80
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_111
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_616
  subst c
  exact valid_inline_518

theorem eq_card_618 : card_618 = combine (5, 5) [placed 1 (2, 3) card_398, placed 0 (1, 2) card_434, placed 4 (6, 1) card_610, inline_513, inline_514, inline_515, inline_516, placed 0 (2, 0) card_615, inline_519] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_618 : Valid card_618 := by
  rw [eq_card_618]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_398
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_434
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_610
  rcases hc with rfl | hc
  · exact valid_inline_513
  rcases hc with rfl | hc
  · exact valid_inline_514
  rcases hc with rfl | hc
  · exact valid_inline_515
  rcases hc with rfl | hc
  · exact valid_inline_516
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_615
  subst c
  exact valid_inline_519

theorem eq_inline_520 : inline_520 = combine (2, 2) [placed 4 (4, 0) card_56, placed 0 (1, 0) card_253] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_520 : Valid inline_520 := by
  rw [eq_inline_520]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_56
  subst c
  exact placed_valid 0 (1, 0) valid_253

theorem eq_card_619 : card_619 = combine (4, 3) [placed 0 (1, 2) card_8, placed 0 (1, 2) card_26, placed 0 (1, 2) card_49, placed 0 (1, 0) card_115, placed 0 (1, 0) card_292, inline_520] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_619 : Valid card_619 := by
  rw [eq_card_619]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_26
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_49
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_292
  subst c
  exact valid_inline_520

theorem eq_inline_521 : inline_521 = combine (3, 3) [placed 6 (4, 6) card_17, placed 6 (4, 6) card_37, placed 3 (4, 3) card_233] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_521 : Valid inline_521 := by
  rw [eq_inline_521]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_37
  subst c
  exact placed_valid 3 (4, 3) valid_233

theorem eq_card_620 : card_620 = combine (4, 5) [placed 3 (6, 3) card_57, placed 7 (6, 7) card_57, placed 3 (6, 3) card_293, placed 7 (6, 7) card_293, inline_521] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_620 : Valid card_620 := by
  rw [eq_card_620]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_57
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 7) valid_57
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_293
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 7) valid_293
  subst c
  exact valid_inline_521

theorem eq_inline_522 : inline_522 = combine (2, 3) [placed 7 (5, 4) card_15, placed 1 (1, 2) card_159, placed 6 (4, 6) card_164] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_522 : Valid inline_522 := by
  rw [eq_inline_522]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_159
  subst c
  exact placed_valid 6 (4, 6) valid_164

theorem eq_inline_523 : inline_523 = combine (1, 4) [placed 2 (0, 4) card_0, placed 2 (0, 6) card_133] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_523 : Valid inline_523 := by
  rw [eq_inline_523]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 4) valid_0
  subst c
  exact placed_valid 2 (0, 6) valid_133

theorem eq_card_621 : card_621 = combine (2, 4) [placed 1 (0, 3) card_206, placed 3 (5, 2) card_238, placed 7 (5, 5) card_414, placed 6 (4, 6) card_417, inline_522, inline_523] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_621 : Valid card_621 := by
  rw [eq_card_621]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_206
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 2) valid_238
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 5) valid_414
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_417
  rcases hc with rfl | hc
  · exact valid_inline_522
  subst c
  exact valid_inline_523

theorem eq_inline_524 : inline_524 = combine (3, 6) [placed 4 (4, 3) card_41, placed 7 (6, 6) card_56] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_524 : Valid inline_524 := by
  rw [eq_inline_524]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_41
  subst c
  exact placed_valid 7 (6, 6) valid_56

theorem eq_inline_525 : inline_525 = combine (3, 6) [placed 7 (3, 6) card_4, placed 4 (4, 3) card_41] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_525 : Valid inline_525 := by
  rw [eq_inline_525]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 6) valid_4
  subst c
  exact placed_valid 4 (4, 3) valid_41

theorem eq_inline_526 : inline_526 = combine (3, 2) [placed 7 (3, 5) card_5, placed 2 (3, 6) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_526 : Valid inline_526 := by
  rw [eq_inline_526]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 5) valid_5
  subst c
  exact placed_valid 2 (3, 6) valid_11

theorem eq_inline_527 : inline_527 = combine (2, 2) [placed 6 (3, 6) card_61, inline_525, inline_526] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_527 : Valid inline_527 := by
  rw [eq_inline_527]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_61
  rcases hc with rfl | hc
  · exact valid_inline_525
  subst c
  exact valid_inline_526

theorem eq_inline_528 : inline_528 = combine (4, 5) [placed 2 (3, 6) card_23, placed 4 (7, 1) card_621] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_528 : Valid inline_528 := by
  rw [eq_inline_528]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_23
  subst c
  exact placed_valid 4 (7, 1) valid_621

theorem eq_card_622 : card_622 = combine (4, 4) [placed 7 (6, 6) card_57, inline_524, inline_527, inline_528] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_622 : Valid card_622 := by
  rw [eq_card_622]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_57
  rcases hc with rfl | hc
  · exact valid_inline_524
  rcases hc with rfl | hc
  · exact valid_inline_527
  subst c
  exact valid_inline_528

theorem eq_inline_529 : inline_529 = combine (5, 5) [placed 4 (7, 3) card_188, placed 0 (4, 4) card_444, placed 2 (4, 9) card_606, placed 2 (4, 9) card_610] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_529 : Valid inline_529 := by
  rw [eq_inline_529]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_444
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 9) valid_606
  subst c
  exact placed_valid 2 (4, 9) valid_610

theorem eq_inline_530 : inline_530 = combine (5, 5) [placed 7 (7, 8) card_137, placed 7 (7, 8) card_181, placed 6 (8, 9) card_363, placed 7 (7, 8) card_474, placed 2 (4, 9) card_606] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_530 : Valid inline_530 := by
  rw [eq_inline_530]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 8) valid_137
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 8) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 9) valid_363
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 8) valid_474
  subst c
  exact placed_valid 2 (4, 9) valid_606

theorem eq_inline_531 : inline_531 = combine (4, 7) [placed 4 (5, 6) card_27, placed 5 (4, 9) card_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_531 : Valid inline_531 := by
  rw [eq_inline_531]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 6) valid_27
  subst c
  exact placed_valid 5 (4, 9) valid_35

theorem eq_inline_532 : inline_532 = combine (5, 9) [placed 2 (4, 10) card_9, placed 4 (8, 5) card_151, placed 4 (6, 4) card_186, placed 4 (5, 4) card_187, inline_531] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_532 : Valid inline_532 := by
  rw [eq_inline_532]
  apply combination_rule (5, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 10) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 5) valid_151
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 4) valid_186
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 4) valid_187
  subst c
  exact valid_inline_531

theorem eq_inline_533 : inline_533 = combine (5, 5) [placed 5 (3, 9) card_179, placed 5 (4, 8) card_371, placed 2 (4, 9) card_443] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_533 : Valid inline_533 := by
  rw [eq_inline_533]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 9) valid_179
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 8) valid_371
  subst c
  exact placed_valid 2 (4, 9) valid_443

theorem eq_inline_534 : inline_534 = combine (5, 8) [placed 4 (6, 4) card_12, placed 4 (7, 4) card_188, placed 4 (8, 4) card_211, inline_532, placed 1 (2, 5) card_619, inline_533, placed 4 (8, 2) card_620] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_534 : Valid inline_534 := by
  rw [eq_inline_534]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 4) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 4) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 4) valid_211
  rcases hc with rfl | hc
  · exact valid_inline_532
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_619
  rcases hc with rfl | hc
  · exact valid_inline_533
  subst c
  exact placed_valid 4 (8, 2) valid_620

theorem eq_inline_535 : inline_535 = combine (5, 5) [placed 5 (3, 9) card_179, placed 5 (4, 8) card_197, placed 0 (4, 4) card_465] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_535 : Valid inline_535 := by
  rw [eq_inline_535]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 9) valid_179
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 8) valid_197
  subst c
  exact placed_valid 0 (4, 4) valid_465

theorem eq_inline_536 : inline_536 = combine (5, 8) [placed 0 (4, 4) card_12, placed 1 (1, 5) card_322, placed 2 (4, 11) card_369, placed 1 (2, 5) card_435, inline_535, placed 6 (8, 11) card_622] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_536 : Valid inline_536 := by
  rw [eq_inline_536]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 5) valid_322
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 11) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_435
  rcases hc with rfl | hc
  · exact valid_inline_535
  subst c
  exact placed_valid 6 (8, 11) valid_622

theorem eq_card_623 : card_623 = combine (5, 6) [placed 6 (9, 11) card_467, placed 1 (0, 3) card_602, placed 4 (6, 3) card_603, placed 3 (8, 4) card_605, placed 6 (9, 11) card_607, placed 6 (9, 11) card_608, inline_529, placed 6 (10, 10) card_618, inline_530, inline_534, inline_536] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_623 : Valid card_623 := by
  rw [eq_card_623]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (9, 11) valid_467
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_602
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_603
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 6 (9, 11) valid_607
  rcases hc with rfl | hc
  · exact placed_valid 6 (9, 11) valid_608
  rcases hc with rfl | hc
  · exact valid_inline_529
  rcases hc with rfl | hc
  · exact placed_valid 6 (10, 10) valid_618
  rcases hc with rfl | hc
  · exact valid_inline_530
  rcases hc with rfl | hc
  · exact valid_inline_534
  subst c
  exact valid_inline_536

theorem eq_inline_537 : inline_537 = combine (4, 3) [placed 5 (0, 4) card_64, placed 4 (4, 2) card_315] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_537 : Valid inline_537 := by
  rw [eq_inline_537]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_64
  subst c
  exact placed_valid 4 (4, 2) valid_315

theorem eq_inline_538 : inline_538 = combine (3, 3) [placed 6 (4, 6) card_10, placed 0 (3, 2) card_52, placed 2 (0, 6) card_82, inline_537] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_538 : Valid inline_538 := by
  rw [eq_inline_538]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_82
  subst c
  exact valid_inline_537

theorem eq_card_624 : card_624 = combine (3, 4) [placed 1 (0, 4) card_54, placed 0 (2, 0) card_545, inline_538] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_624 : Valid card_624 := by
  rw [eq_card_624]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_545
  subst c
  exact valid_inline_538

theorem eq_inline_539 : inline_539 = combine (3, 1) [placed 7 (6, 4) card_56, placed 4 (4, 0) card_73] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_539 : Valid inline_539 := by
  rw [eq_inline_539]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_56
  subst c
  exact placed_valid 4 (4, 0) valid_73

theorem eq_inline_540 : inline_540 = combine (3, 4) [placed 4 (4, 1) card_10, placed 0 (0, 1) card_82, inline_539] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_540 : Valid inline_540 := by
  rw [eq_inline_540]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_82
  subst c
  exact valid_inline_539

theorem eq_inline_541 : inline_541 = combine (3, 3) [placed 5 (0, 3) card_54, placed 3 (6, 1) card_294, placed 1 (0, 0) card_449, inline_540] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_541 : Valid inline_541 := by
  rw [eq_inline_541]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 1) valid_294
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_449
  subst c
  exact valid_inline_540

theorem eq_card_625 : card_625 = combine (3, 2) [placed 5 (0, 3) card_50, placed 5 (0, 3) card_125, placed 3 (5, 1) card_454, placed 0 (1, 1) card_455, inline_541] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_625 : Valid card_625 := by
  rw [eq_card_625]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_125
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 1) valid_454
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_455
  subst c
  exact valid_inline_541

theorem eq_inline_542 : inline_542 = combine (2, 5) [placed 0 (2, 5) card_5, placed 6 (5, 6) card_38] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_542 : Valid inline_542 := by
  rw [eq_inline_542]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_5
  subst c
  exact placed_valid 6 (5, 6) valid_38

theorem eq_inline_543 : inline_543 = combine (4, 5) [placed 2 (2, 9) card_317, inline_542, placed 0 (2, 2) card_519] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_543 : Valid inline_543 := by
  rw [eq_inline_543]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_317
  rcases hc with rfl | hc
  · exact valid_inline_542
  subst c
  exact placed_valid 0 (2, 2) valid_519

theorem eq_inline_544 : inline_544 = combine (2, 5) [placed 6 (5, 6) card_5, placed 1 (1, 5) card_412] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_544 : Valid inline_544 := by
  rw [eq_inline_544]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_5
  subst c
  exact placed_valid 1 (1, 5) valid_412

theorem eq_inline_545 : inline_545 = combine (4, 6) [placed 5 (1, 6) card_11, placed 1 (2, 5) card_336, inline_544] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_545 : Valid inline_545 := by
  rw [eq_inline_545]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_336
  subst c
  exact valid_inline_544

theorem eq_card_626 : card_626 = combine (5, 6) [placed 4 (6, 2) card_323, placed 0 (2, 2) card_430, placed 7 (6, 6) card_592, inline_543, inline_545] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_626 : Valid card_626 := by
  rw [eq_card_626]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_323
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_430
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_592
  rcases hc with rfl | hc
  · exact valid_inline_543
  subst c
  exact valid_inline_545

theorem eq_inline_546 : inline_546 = combine (4, 4) [placed 2 (3, 4) card_5, placed 4 (7, 2) card_472] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_546 : Valid inline_546 := by
  rw [eq_inline_546]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 4) valid_5
  subst c
  exact placed_valid 4 (7, 2) valid_472

theorem eq_inline_547 : inline_547 = combine (5, 3) [placed 7 (6, 6) card_38, placed 6 (6, 7) card_205] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_547 : Valid inline_547 := by
  rw [eq_inline_547]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_38
  subst c
  exact placed_valid 6 (6, 7) valid_205

theorem eq_inline_548 : inline_548 = combine (5, 5) [placed 5 (5, 7) card_0, inline_547] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_548 : Valid inline_548 := by
  rw [eq_inline_548]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 7) valid_0
  subst c
  exact valid_inline_547

theorem eq_inline_549 : inline_549 = combine (5, 3) [placed 7 (6, 6) card_38, placed 5 (3, 7) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_549 : Valid inline_549 := by
  rw [eq_inline_549]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_38
  subst c
  exact placed_valid 5 (3, 7) valid_179

theorem eq_inline_550 : inline_550 = combine (5, 5) [placed 5 (5, 7) card_0, inline_549] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_550 : Valid inline_550 := by
  rw [eq_inline_550]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 7) valid_0
  subst c
  exact valid_inline_549

theorem eq_inline_551 : inline_551 = combine (5, 7) [placed 4 (6, 3) card_50, placed 4 (6, 3) card_97, placed 0 (5, 3) card_98, placed 2 (4, 8) card_454, placed 1 (4, 4) card_455, placed 3 (10, 3) card_624] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_551 : Valid inline_551 := by
  rw [eq_inline_551]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_97
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_98
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_454
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_455
  subst c
  exact placed_valid 3 (10, 3) valid_624

theorem eq_inline_552 : inline_552 = combine (5, 3) [placed 7 (6, 6) card_38, placed 0 (4, 2) card_413] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_552 : Valid inline_552 := by
  rw [eq_inline_552]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_38
  subst c
  exact placed_valid 0 (4, 2) valid_413

theorem eq_inline_553 : inline_553 = combine (5, 5) [placed 5 (5, 7) card_0, inline_552] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_553 : Valid inline_553 := by
  rw [eq_inline_553]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 7) valid_0
  subst c
  exact valid_inline_552

theorem eq_inline_554 : inline_554 = combine (6, 6) [placed 3 (9, 3) card_59, placed 4 (6, 2) card_105, placed 5 (2, 7) card_323, placed 1 (2, 5) card_603] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_554 : Valid inline_554 := by
  rw [eq_inline_554]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 3) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_105
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_323
  subst c
  exact placed_valid 1 (2, 5) valid_603

theorem eq_inline_555 : inline_555 = combine (5, 6) [inline_548, inline_550, inline_551, placed 1 (0, 1) card_626, inline_553, inline_554] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_555 : Valid inline_555 := by
  rw [eq_inline_555]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_548
  rcases hc with rfl | hc
  · exact valid_inline_550
  rcases hc with rfl | hc
  · exact valid_inline_551
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_626
  rcases hc with rfl | hc
  · exact valid_inline_553
  subst c
  exact valid_inline_554

theorem eq_card_627 : card_627 = combine (5, 4) [placed 7 (7, 4) card_34, placed 0 (2, 2) card_478, inline_546, inline_555] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_627 : Valid card_627 := by
  rw [eq_card_627]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 4) valid_34
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_478
  rcases hc with rfl | hc
  · exact valid_inline_546
  subst c
  exact valid_inline_555

theorem eq_inline_556 : inline_556 = combine (3, 2) [placed 7 (4, 3) card_36, placed 0 (3, 0) card_53] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_556 : Valid inline_556 := by
  rw [eq_inline_556]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 3) valid_36
  subst c
  exact placed_valid 0 (3, 0) valid_53

theorem eq_inline_557 : inline_557 = combine (3, 4) [placed 7 (5, 4) card_34, placed 4 (4, 0) card_464] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_557 : Valid inline_557 := by
  rw [eq_inline_557]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_34
  subst c
  exact placed_valid 4 (4, 0) valid_464

theorem eq_inline_558 : inline_558 = combine (2, 3) [placed 6 (4, 3) card_5, placed 5 (1, 4) card_265] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_558 : Valid inline_558 := by
  rw [eq_inline_558]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_5
  subst c
  exact placed_valid 5 (1, 4) valid_265

theorem eq_card_628 : card_628 = combine (3, 3) [placed 1 (0, 2) card_126, placed 2 (1, 5) card_270, inline_556, inline_557, inline_558] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_628 : Valid card_628 := by
  rw [eq_card_628]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_126
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_270
  rcases hc with rfl | hc
  · exact valid_inline_556
  rcases hc with rfl | hc
  · exact valid_inline_557
  subst c
  exact valid_inline_558

theorem eq_card_629 : card_629 = combine (3, 5) [placed 4 (5, 1) card_190, placed 4 (7, 2) card_295, placed 4 (6, 1) card_364, placed 0 (0, 0) card_518, placed 2 (2, 7) card_628] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_629 : Valid card_629 := by
  rw [eq_card_629]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_295
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_364
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_518
  subst c
  exact placed_valid 2 (2, 7) valid_628

theorem eq_inline_559 : inline_559 = combine (4, 8) [placed 0 (3, 4) card_12, placed 6 (5, 10) card_13, placed 6 (7, 9) card_355, placed 6 (7, 10) card_356, placed 4 (8, 5) card_434, placed 3 (7, 5) card_435, placed 2 (3, 10) card_441] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_559 : Valid inline_559 := by
  rw [eq_inline_559]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 10) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 9) valid_355
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 10) valid_356
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 5) valid_434
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 5) valid_435
  subst c
  exact placed_valid 2 (3, 10) valid_441

theorem eq_inline_560 : inline_560 = combine (4, 5) [placed 0 (3, 3) card_13, placed 0 (3, 4) card_112, placed 6 (7, 9) card_363, placed 6 (7, 9) card_364] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_560 : Valid inline_560 := by
  rw [eq_inline_560]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_112
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 9) valid_363
  subst c
  exact placed_valid 6 (7, 9) valid_364

theorem eq_inline_561 : inline_561 = combine (4, 5) [placed 0 (3, 4) card_112, placed 3 (6, 4) card_181, placed 5 (2, 8) card_181, placed 6 (8, 8) card_295, placed 0 (3, 4) card_466] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_561 : Valid inline_561 := by
  rw [eq_inline_561]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_112
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 8) valid_295
  subst c
  exact placed_valid 0 (3, 4) valid_466

theorem eq_inline_562 : inline_562 = combine (5, 7) [placed 6 (5, 8) card_10, placed 5 (3, 7) card_34] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_562 : Valid inline_562 := by
  rw [eq_inline_562]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_10
  subst c
  exact placed_valid 5 (3, 7) valid_34

theorem eq_inline_563 : inline_563 = combine (4, 5) [placed 0 (3, 4) card_112, placed 5 (1, 8) card_257, placed 7 (7, 7) card_398, inline_562, placed 0 (3, 3) card_628] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_563 : Valid inline_563 := by
  rw [eq_inline_563]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_112
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 8) valid_257
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 7) valid_398
  rcases hc with rfl | hc
  · exact valid_inline_562
  subst c
  exact placed_valid 0 (3, 3) valid_628

theorem eq_card_630 : card_630 = combine (4, 6) [placed 4 (8, 3) card_368, placed 6 (8, 10) card_368, inline_559, placed 6 (8, 11) card_467, placed 0 (1, 3) card_627, inline_560, inline_561, placed 2 (1, 10) card_629, inline_563] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_630 : Valid card_630 := by
  rw [eq_card_630]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_368
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 10) valid_368
  rcases hc with rfl | hc
  · exact valid_inline_559
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 11) valid_467
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_627
  rcases hc with rfl | hc
  · exact valid_inline_560
  rcases hc with rfl | hc
  · exact valid_inline_561
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_629
  subst c
  exact valid_inline_563

theorem eq_inline_564 : inline_564 = combine (3, 2) [placed 7 (5, 5) card_45, placed 1 (2, 2) card_418] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_564 : Valid inline_564 := by
  rw [eq_inline_564]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 5) valid_45
  subst c
  exact placed_valid 1 (2, 2) valid_418

theorem eq_inline_565 : inline_565 = combine (4, 2) [placed 2 (3, 5) card_43, placed 2 (3, 5) card_51, inline_564] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_565 : Valid inline_565 := by
  rw [eq_inline_565]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_43
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_51
  subst c
  exact valid_inline_564

theorem eq_card_631 : card_631 = combine (3, 5) [placed 2 (3, 6) card_44, placed 2 (3, 6) card_52, placed 4 (4, 2) card_63, inline_565] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_631 : Valid card_631 := by
  rw [eq_card_631]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_63
  subst c
  exact valid_inline_565

theorem eq_inline_566 : inline_566 = combine (3, 2) [placed 5 (1, 5) card_92, placed 1 (1, 2) card_378] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_566 : Valid inline_566 := by
  rw [eq_inline_566]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_92
  subst c
  exact placed_valid 1 (1, 2) valid_378

theorem eq_inline_567 : inline_567 = combine (3, 5) [placed 4 (4, 2) card_10, placed 2 (3, 6) card_52, placed 0 (0, 2) card_82, inline_566] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_567 : Valid inline_567 := by
  rw [eq_inline_567]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_82
  subst c
  exact valid_inline_566

theorem eq_inline_568 : inline_568 = combine (3, 4) [placed 5 (0, 4) card_54, placed 3 (6, 2) card_294, inline_567, placed 0 (0, 0) card_631] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_568 : Valid inline_568 := by
  rw [eq_inline_568]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_294
  rcases hc with rfl | hc
  · exact valid_inline_567
  subst c
  exact placed_valid 0 (0, 0) valid_631

theorem eq_card_632 : card_632 = combine (3, 3) [placed 5 (0, 4) card_50, placed 5 (0, 4) card_125, placed 3 (5, 2) card_454, placed 0 (1, 2) card_455, inline_568] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_632 : Valid card_632 := by
  rw [eq_card_632]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_125
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 2) valid_454
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_455
  subst c
  exact valid_inline_568

theorem eq_inline_569 : inline_569 = combine (5, 3) [placed 1 (4, 3) card_8, placed 5 (4, 6) card_93] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_569 : Valid inline_569 := by
  rw [eq_inline_569]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 3) valid_8
  subst c
  exact placed_valid 5 (4, 6) valid_93

theorem eq_inline_570 : inline_570 = combine (5, 6) [placed 4 (5, 3) card_27, placed 6 (5, 7) card_52, placed 5 (3, 6) card_144, inline_569] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_570 : Valid inline_570 := by
  rw [eq_inline_570]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_144
  subst c
  exact valid_inline_569

theorem eq_card_633 : card_633 = combine (4, 4) [placed 6 (6, 6) card_47, placed 6 (5, 6) card_144, inline_570] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_633 : Valid card_633 := by
  rw [eq_card_633]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 6) valid_47
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_144
  subst c
  exact valid_inline_570

theorem eq_card_634 : card_634 = combine (5, 5) [placed 0 (0, 1) card_438, placed 0 (0, 1) card_452, placed 2 (3, 8) card_587, placed 7 (6, 5) card_612, placed 0 (0, 0) card_633] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_634 : Valid card_634 := by
  rw [eq_card_634]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_438
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_452
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_612
  subst c
  exact placed_valid 0 (0, 0) valid_633

theorem eq_inline_571 : inline_571 = combine (2, 6) [placed 4 (2, 2) card_7, placed 0 (1, 2) card_9, placed 1 (0, 3) card_395] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_571 : Valid inline_571 := by
  rw [eq_inline_571]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_9
  subst c
  exact placed_valid 1 (0, 3) valid_395

theorem eq_card_635 : card_635 = combine (2, 3) [placed 2 (1, 7) card_14, placed 6 (3, 7) card_33, placed 5 (0, 6) card_181, placed 5 (0, 6) card_589, inline_571] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_635 : Valid card_635 := by
  rw [eq_card_635]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 7) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_589
  subst c
  exact valid_inline_571

theorem eq_inline_572 : inline_572 = combine (3, 5) [placed 7 (5, 5) card_22, placed 6 (5, 7) card_108, placed 0 (2, 1) card_512] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_572 : Valid inline_572 := by
  rw [eq_inline_572]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 5) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_108
  subst c
  exact placed_valid 0 (2, 1) valid_512

theorem eq_inline_573 : inline_573 = combine (4, 6) [placed 0 (3, 3) card_10, placed 6 (4, 7) card_44, placed 0 (3, 3) card_63, placed 5 (1, 7) card_117] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_573 : Valid inline_573 := by
  rw [eq_inline_573]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_63
  subst c
  exact placed_valid 5 (1, 7) valid_117

theorem eq_inline_574 : inline_574 = combine (5, 5) [placed 0 (3, 1) card_85, placed 0 (3, 2) card_164, placed 2 (2, 7) card_262] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_574 : Valid inline_574 := by
  rw [eq_inline_574]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_85
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_164
  subst c
  exact placed_valid 2 (2, 7) valid_262

theorem eq_inline_575 : inline_575 = combine (3, 5) [placed 2 (1, 5) card_1, inline_574] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_575 : Valid inline_575 := by
  rw [eq_inline_575]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_1
  subst c
  exact valid_inline_574

theorem eq_inline_576 : inline_576 = combine (6, 4) [placed 5 (2, 4) card_7, placed 1 (2, 4) card_11, placed 4 (6, 1) card_331] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_576 : Valid inline_576 := by
  rw [eq_inline_576]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_11
  subst c
  exact placed_valid 4 (6, 1) valid_331

theorem eq_inline_577 : inline_577 = combine (5, 4) [placed 0 (2, 1) card_332, placed 2 (2, 6) card_474, placed 0 (2, 2) card_522, inline_575, inline_576] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_577 : Valid inline_577 := by
  rw [eq_inline_577]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_332
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_474
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_522
  rcases hc with rfl | hc
  · exact valid_inline_575
  subst c
  exact valid_inline_576

theorem eq_inline_578 : inline_578 = combine (4, 5) [placed 2 (2, 8) card_399, placed 0 (3, 1) card_408, placed 2 (2, 8) card_475, placed 1 (1, 2) card_509, placed 0 (2, 1) card_587, inline_572, placed 2 (2, 9) card_635, inline_573, inline_577] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_578 : Valid inline_578 := by
  rw [eq_inline_578]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_399
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_408
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_475
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_509
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_587
  rcases hc with rfl | hc
  · exact valid_inline_572
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_635
  rcases hc with rfl | hc
  · exact valid_inline_573
  subst c
  exact valid_inline_577

theorem eq_inline_579 : inline_579 = combine (5, 4) [placed 0 (2, 1) card_118, placed 1 (1, 2) card_188, placed 5 (1, 6) card_188, placed 1 (1, 3) card_192, placed 1 (1, 3) card_193, placed 3 (8, 2) card_396] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_579 : Valid inline_579 := by
  rw [eq_inline_579]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_118
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_193
  subst c
  exact placed_valid 3 (8, 2) valid_396

theorem eq_card_636 : card_636 = combine (3, 4) [placed 5 (0, 5) card_125, placed 3 (5, 3) card_454, inline_578, inline_579] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_636 : Valid card_636 := by
  rw [eq_card_636]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_125
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_454
  rcases hc with rfl | hc
  · exact valid_inline_578
  subst c
  exact valid_inline_579

theorem eq_inline_580 : inline_580 = combine (4, 4) [placed 6 (4, 5) card_15, placed 1 (1, 3) card_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_580 : Valid inline_580 := by
  rw [eq_inline_580]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_15
  subst c
  exact placed_valid 1 (1, 3) valid_44

theorem eq_inline_581 : inline_581 = combine (3, 3) [placed 0 (0, 2) card_0, inline_580] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_581 : Valid inline_581 := by
  rw [eq_inline_581]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_0
  subst c
  exact valid_inline_580

theorem eq_inline_582 : inline_582 = combine (4, 3) [placed 0 (1, 2) card_5, inline_581] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_582 : Valid inline_582 := by
  rw [eq_inline_582]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_5
  subst c
  exact valid_inline_581

theorem eq_card_637 : card_637 = combine (4, 2) [placed 1 (1, 2) card_21, placed 5 (1, 3) card_41, placed 5 (1, 3) card_48, inline_582] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_637 : Valid card_637 := by
  rw [eq_card_637]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 3) valid_41
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 3) valid_48
  subst c
  exact valid_inline_582

theorem eq_inline_583 : inline_583 = combine (3, 4) [placed 1 (0, 3) card_15, placed 2 (1, 7) card_85] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_583 : Valid inline_583 := by
  rw [eq_inline_583]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_15
  subst c
  exact placed_valid 2 (1, 7) valid_85

theorem eq_card_638 : card_638 = combine (3, 3) [placed 2 (0, 6) card_57, placed 5 (0, 5) card_136, placed 5 (0, 5) card_217, placed 0 (1, 0) card_530, inline_583, placed 0 (0, 1) card_637] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_638 : Valid card_638 := by
  rw [eq_card_638]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_57
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_136
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_217
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_530
  rcases hc with rfl | hc
  · exact valid_inline_583
  subst c
  exact placed_valid 0 (0, 1) valid_637

theorem eq_inline_584 : inline_584 = combine (3, 6) [placed 0 (3, 3) card_21, placed 4 (4, 3) card_37, placed 6 (4, 7) card_62] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_584 : Valid inline_584 := by
  rw [eq_inline_584]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_37
  subst c
  exact placed_valid 6 (4, 7) valid_62

theorem eq_inline_585 : inline_585 = combine (3, 5) [placed 4 (4, 2) card_71, placed 6 (4, 6) card_73, inline_584, placed 6 (4, 6) card_451] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_585 : Valid inline_585 := by
  rw [eq_inline_585]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_71
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_73
  rcases hc with rfl | hc
  · exact valid_inline_584
  subst c
  exact placed_valid 6 (4, 6) valid_451

theorem eq_inline_586 : inline_586 = combine (3, 5) [placed 4 (4, 2) card_71, placed 6 (4, 6) card_73, placed 3 (6, 2) card_435, placed 6 (4, 6) card_451] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_586 : Valid inline_586 := by
  rw [eq_inline_586]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_71
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_73
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_435
  subst c
  exact placed_valid 6 (4, 6) valid_451

theorem eq_inline_587 : inline_587 = combine (3, 3) [placed 1 (0, 3) card_54, placed 1 (0, 2) card_638, inline_585, inline_586] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_587 : Valid inline_587 := by
  rw [eq_inline_587]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_638
  rcases hc with rfl | hc
  · exact valid_inline_585
  subst c
  exact valid_inline_586

theorem eq_card_639 : card_639 = combine (3, 4) [placed 1 (0, 3) card_50, placed 1 (0, 3) card_125, placed 0 (0, 2) card_478, placed 0 (0, 2) card_482, inline_587] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_639 : Valid card_639 := by
  rw [eq_card_639]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_125
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_478
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_482
  subst c
  exact valid_inline_587

theorem block09_valid : Valid card_576 ∧ Valid card_577 ∧ Valid card_578 ∧ Valid card_579 ∧ Valid card_580 ∧ Valid card_581 ∧ Valid card_582 ∧ Valid card_583 ∧ Valid card_584 ∧ Valid card_585 ∧ Valid card_586 ∧ Valid card_587 ∧ Valid card_588 ∧ Valid card_589 ∧ Valid card_590 ∧ Valid card_591 ∧ Valid card_592 ∧ Valid card_593 ∧ Valid card_594 ∧ Valid card_595 ∧ Valid card_596 ∧ Valid card_597 ∧ Valid card_598 ∧ Valid card_599 ∧ Valid card_600 ∧ Valid card_601 ∧ Valid card_602 ∧ Valid card_603 ∧ Valid card_604 ∧ Valid card_605 ∧ Valid card_606 ∧ Valid card_607 ∧ Valid card_608 ∧ Valid card_609 ∧ Valid card_610 ∧ Valid card_611 ∧ Valid card_612 ∧ Valid card_613 ∧ Valid card_614 ∧ Valid card_615 ∧ Valid card_616 ∧ Valid card_617 ∧ Valid card_618 ∧ Valid card_619 ∧ Valid card_620 ∧ Valid card_621 ∧ Valid card_622 ∧ Valid card_623 ∧ Valid card_624 ∧ Valid card_625 ∧ Valid card_626 ∧ Valid card_627 ∧ Valid card_628 ∧ Valid card_629 ∧ Valid card_630 ∧ Valid card_631 ∧ Valid card_632 ∧ Valid card_633 ∧ Valid card_634 ∧ Valid card_635 ∧ Valid card_636 ∧ Valid card_637 ∧ Valid card_638 ∧ Valid card_639 ∧ True :=
  ⟨valid_576, valid_577, valid_578, valid_579, valid_580, valid_581, valid_582, valid_583, valid_584, valid_585, valid_586, valid_587, valid_588, valid_589, valid_590, valid_591, valid_592, valid_593, valid_594, valid_595, valid_596, valid_597, valid_598, valid_599, valid_600, valid_601, valid_602, valid_603, valid_604, valid_605, valid_606, valid_607, valid_608, valid_609, valid_610, valid_611, valid_612, valid_613, valid_614, valid_615, valid_616, valid_617, valid_618, valid_619, valid_620, valid_621, valid_622, valid_623, valid_624, valid_625, valid_626, valid_627, valid_628, valid_629, valid_630, valid_631, valid_632, valid_633, valid_634, valid_635, valid_636, valid_637, valid_638, valid_639, True.intro⟩

end OAI.Snaky21.Certificate
