import Definitions.Def_Snaky21Data08
import Solutions.Snaky21.Geometry
import Solutions.Snaky21.Certificate07

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_inline_157 : inline_157 = combine (3, 3) [placed 4 (4, 1) card_69, placed 0 (1, 1) card_416] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_157 : Valid inline_157 := by
  rw [eq_inline_157]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_69
  subst c
  exact placed_valid 0 (1, 1) valid_416

theorem eq_inline_158 : inline_158 = combine (3, 4) [placed 6 (5, 4) card_0, placed 0 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_158 : Valid inline_158 := by
  rw [eq_inline_158]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_0
  subst c
  exact placed_valid 0 (1, 4) valid_5

theorem eq_inline_159 : inline_159 = combine (3, 6) [placed 2 (3, 6) card_18, placed 0 (1, 2) card_382] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_159 : Valid inline_159 := by
  rw [eq_inline_159]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_18
  subst c
  exact placed_valid 0 (1, 2) valid_382

theorem eq_inline_160 : inline_160 = combine (4, 5) [inline_158, inline_159] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_160 : Valid inline_160 := by
  rw [eq_inline_160]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_158
  subst c
  exact valid_inline_159

theorem eq_inline_161 : inline_161 = combine (4, 4) [placed 5 (1, 4) card_30, placed 2 (1, 7) card_59, placed 0 (1, 1) card_511, inline_160] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_161 : Valid inline_161 := by
  rw [eq_inline_161]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_30
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_511
  subst c
  exact valid_inline_160

theorem eq_card_512 : card_512 = combine (4, 3) [placed 1 (1, 3) card_74, placed 0 (0, 1) card_108, inline_157, inline_161] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_512 : Valid card_512 := by
  rw [eq_card_512]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_74
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_108
  rcases hc with rfl | hc
  · exact valid_inline_157
  subst c
  exact valid_inline_161

theorem eq_inline_162 : inline_162 = combine (0, 4) [placed 3 (1, 1) card_5, placed 3 (5, 1) card_439] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_162 : Valid inline_162 := by
  rw [eq_inline_162]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 1) valid_5
  subst c
  exact placed_valid 3 (5, 1) valid_439

theorem eq_card_513 : card_513 = combine (1, 4) [placed 4 (1, 0) card_7, placed 0 (0, 0) card_9, inline_162] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_513 : Valid card_513 := by
  rw [eq_card_513]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_9
  subst c
  exact valid_inline_162

theorem eq_card_514 : card_514 = combine (3, 2) [placed 7 (5, 2) card_34, placed 3 (5, 1) card_149, placed 0 (0, 0) card_513] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_514 : Valid card_514 := by
  rw [eq_card_514]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 2) valid_34
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 1) valid_149
  subst c
  exact placed_valid 0 (0, 0) valid_513

theorem eq_inline_163 : inline_163 = combine (3, 1) [placed 6 (4, 1) card_0, placed 0 (0, 0) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_163 : Valid inline_163 := by
  rw [eq_inline_163]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 1) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_78

theorem eq_card_515 : card_515 = combine (2, 1) [placed 7 (2, 4) card_2, inline_163] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_515 : Valid card_515 := by
  rw [eq_card_515]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 4) valid_2
  subst c
  exact valid_inline_163

theorem eq_inline_164 : inline_164 = combine (2, 3) [placed 6 (4, 3) card_3, placed 6 (4, 4) card_83] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_164 : Valid inline_164 := by
  rw [eq_inline_164]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_3
  subst c
  exact placed_valid 6 (4, 4) valid_83

theorem eq_card_516 : card_516 = combine (4, 3) [placed 0 (3, 0) card_52, inline_164, placed 1 (0, 1) card_515] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_516 : Valid card_516 := by
  rw [eq_card_516]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_52
  rcases hc with rfl | hc
  · exact valid_inline_164
  subst c
  exact placed_valid 1 (0, 1) valid_515

theorem eq_inline_165 : inline_165 = combine (3, 4) [placed 6 (5, 4) card_0, placed 1 (0, 3) card_404] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_165 : Valid inline_165 := by
  rw [eq_inline_165]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_0
  subst c
  exact placed_valid 1 (0, 3) valid_404

theorem eq_inline_166 : inline_166 = combine (4, 5) [placed 6 (5, 7) card_14, placed 2 (1, 6) card_79, placed 2 (3, 7) card_367, placed 4 (5, 2) card_513, placed 0 (1, 2) card_516] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_166 : Valid inline_166 := by
  rw [eq_inline_166]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_367
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_513
  subst c
  exact placed_valid 0 (1, 2) valid_516

theorem eq_inline_167 : inline_167 = combine (4, 3) [placed 1 (1, 3) card_30, placed 0 (1, 0) card_59, placed 2 (1, 6) card_346, inline_166] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_167 : Valid inline_167 := by
  rw [eq_inline_167]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_30
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_346
  subst c
  exact valid_inline_166

theorem eq_inline_168 : inline_168 = combine (4, 5) [placed 2 (3, 7) card_14, placed 0 (1, 2) card_58, placed 2 (1, 6) card_79, placed 0 (1, 2) card_429] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_168 : Valid inline_168 := by
  rw [eq_inline_168]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_58
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_79
  subst c
  exact placed_valid 0 (1, 2) valid_429

theorem eq_inline_169 : inline_169 = combine (4, 3) [placed 5 (1, 4) card_36, placed 2 (1, 7) card_59, placed 2 (1, 6) card_346, inline_168] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_169 : Valid inline_169 := by
  rw [eq_inline_169]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_36
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_346
  subst c
  exact valid_inline_168

theorem eq_card_517 : card_517 = combine (4, 4) [placed 5 (1, 4) card_74, inline_165, inline_167, inline_169] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_517 : Valid card_517 := by
  rw [eq_card_517]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_74
  rcases hc with rfl | hc
  · exact valid_inline_165
  rcases hc with rfl | hc
  · exact valid_inline_167
  subst c
  exact valid_inline_169

theorem eq_inline_170 : inline_170 = combine (3, 7) [placed 4 (3, 3) card_6, placed 3 (6, 4) card_213, placed 1 (1, 4) card_278] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_170 : Valid inline_170 := by
  rw [eq_inline_170]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 3) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_213
  subst c
  exact placed_valid 1 (1, 4) valid_278

theorem eq_inline_171 : inline_171 = combine (3, 6) [placed 1 (3, 3) card_5, inline_170] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_171 : Valid inline_171 := by
  rw [eq_inline_171]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_5
  subst c
  exact valid_inline_170

theorem eq_card_518 : card_518 = combine (4, 6) [placed 0 (3, 2) card_61, placed 6 (4, 6) card_89, placed 1 (1, 2) card_183, inline_171] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_518 : Valid card_518 := by
  rw [eq_card_518]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_61
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_89
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_183
  subst c
  exact valid_inline_171

theorem eq_card_519 : card_519 = combine (3, 5) [placed 0 (2, 2) card_10, placed 5 (1, 6) card_47, placed 6 (3, 6) card_52, placed 4 (6, 0) card_518] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_519 : Valid card_519 := by
  rw [eq_card_519]
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
  exact placed_valid 4 (6, 0) valid_518

theorem eq_card_520 : card_520 = combine (4, 5) [placed 5 (2, 6) card_10, placed 6 (6, 9) card_317, placed 4 (6, 2) card_519] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_520 : Valid card_520 := by
  rw [eq_card_520]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 9) valid_317
  subst c
  exact placed_valid 4 (6, 2) valid_519

theorem eq_inline_172 : inline_172 = combine (2, 3) [placed 1 (0, 1) card_45, placed 5 (0, 4) card_45] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_172 : Valid inline_172 := by
  rw [eq_inline_172]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_45
  subst c
  exact placed_valid 5 (0, 4) valid_45

theorem eq_inline_173 : inline_173 = combine (2, 4) [placed 1 (1, 1) card_5, inline_172] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_173 : Valid inline_173 := by
  rw [eq_inline_173]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_172

theorem eq_card_521 : card_521 = combine (2, 1) [placed 5 (1, 4) card_5, inline_173] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_521 : Valid card_521 := by
  rw [eq_card_521]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact valid_inline_173

theorem eq_inline_174 : inline_174 = combine (1, 3) [placed 4 (4, 2) card_5, placed 0 (1, 0) card_416] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_174 : Valid inline_174 := by
  rw [eq_inline_174]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_416

theorem eq_card_522 : card_522 = combine (4, 2) [placed 0 (1, 1) card_8, placed 1 (0, 2) card_11, inline_174] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_522 : Valid card_522 := by
  rw [eq_card_522]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_11
  subst c
  exact valid_inline_174

theorem eq_card_523 : card_523 = combine (3, 5) [placed 0 (2, 1) card_14, placed 0 (1, 2) card_122, placed 2 (1, 6) card_136, placed 4 (4, 1) card_367, placed 7 (5, 6) card_522] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_523 : Valid card_523 := by
  rw [eq_card_523]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_122
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_136
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_367
  subst c
  exact placed_valid 7 (5, 6) valid_522

theorem eq_card_524 : card_524 = combine (3, 5) [placed 5 (0, 6) card_88, placed 1 (0, 2) card_213, placed 0 (2, 1) card_254, placed 7 (5, 6) card_522] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_524 : Valid card_524 := by
  rw [eq_card_524]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_88
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_213
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_254
  subst c
  exact placed_valid 7 (5, 6) valid_522

theorem eq_inline_175 : inline_175 = combine (3, 3) [placed 4 (3, 0) card_21, placed 0 (2, 0) card_37, placed 3 (4, 0) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_175 : Valid inline_175 := by
  rw [eq_inline_175]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_37
  subst c
  exact placed_valid 3 (4, 0) valid_78

theorem eq_inline_176 : inline_176 = combine (3, 2) [placed 0 (0, 1) card_5, inline_175] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_176 : Valid inline_176 := by
  rw [eq_inline_176]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_175

theorem eq_card_525 : card_525 = combine (3, 0) [placed 2 (0, 1) card_5, inline_176] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_525 : Valid card_525 := by
  rw [eq_card_525]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact valid_inline_176

theorem eq_card_526 : card_526 = combine (3, 1) [placed 4 (4, 1) card_0, placed 0 (0, 0) card_525] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_526 : Valid card_526 := by
  rw [eq_card_526]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_525

theorem eq_inline_177 : inline_177 = combine (2, 5) [placed 4 (2, 2) card_23, placed 2 (1, 6) card_198] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_177 : Valid inline_177 := by
  rw [eq_inline_177]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_23
  subst c
  exact placed_valid 2 (1, 6) valid_198

theorem eq_inline_178 : inline_178 = combine (3, 3) [placed 2 (1, 6) card_392, placed 0 (1, 1) card_417, placed 0 (1, 2) card_420, placed 0 (1, 1) card_521, placed 2 (0, 5) card_522, placed 0 (1, 2) card_526] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_178 : Valid inline_178 := by
  rw [eq_inline_178]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_392
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_417
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_420
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_521
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_522
  subst c
  exact placed_valid 0 (1, 2) valid_526

theorem eq_inline_179 : inline_179 = combine (2, 5) [placed 0 (2, 1) card_7, placed 4 (2, 2) card_23, inline_178] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_179 : Valid inline_179 := by
  rw [eq_inline_179]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_23
  subst c
  exact valid_inline_178

theorem eq_card_527 : card_527 = combine (2, 2) [placed 0 (1, 0) card_206, inline_177, placed 2 (1, 5) card_405, inline_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_527 : Valid card_527 := by
  rw [eq_card_527]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_206
  rcases hc with rfl | hc
  · exact valid_inline_177
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_405
  subst c
  exact valid_inline_179

theorem eq_inline_180 : inline_180 = combine (1, 3) [placed 3 (1, 3) card_4, placed 7 (2, 6) card_49] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_180 : Valid inline_180 := by
  rw [eq_inline_180]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 3) valid_4
  subst c
  exact placed_valid 7 (2, 6) valid_49

theorem eq_inline_181 : inline_181 = combine (1, 7) [placed 3 (1, 4) card_5, placed 0 (0, 1) card_446] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_181 : Valid inline_181 := by
  rw [eq_inline_181]
  apply combination_rule (1, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 4) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_446

theorem eq_card_528 : card_528 = combine (0, 7) [placed 4 (1, 3) card_61, inline_180, inline_181] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_528 : Valid card_528 := by
  rw [eq_card_528]
  apply combination_rule (0, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 3) valid_61
  rcases hc with rfl | hc
  · exact valid_inline_180
  subst c
  exact valid_inline_181

theorem eq_inline_182 : inline_182 = combine (3, 6) [placed 6 (6, 6) card_4, placed 2 (3, 6) card_4] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_182 : Valid inline_182 := by
  rw [eq_inline_182]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 6) valid_4
  subst c
  exact placed_valid 2 (3, 6) valid_4

theorem eq_inline_183 : inline_183 = combine (7, 3) [placed 5 (4, 6) card_38, placed 2 (4, 7) card_351] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_183 : Valid inline_183 := by
  rw [eq_inline_183]
  apply combination_rule (7, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 6) valid_38
  subst c
  exact placed_valid 2 (4, 7) valid_351

theorem eq_inline_184 : inline_184 = combine (7, 5) [inline_182, inline_183] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_184 : Valid inline_184 := by
  rw [eq_inline_184]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_182
  subst c
  exact valid_inline_183

theorem eq_inline_185 : inline_185 = combine (4, 6) [placed 3 (5, 3) card_5, inline_184] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_185 : Valid inline_185 := by
  rw [eq_inline_185]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_5
  subst c
  exact valid_inline_184

theorem eq_inline_186 : inline_186 = combine (6, 6) [placed 1 (5, 3) card_5, inline_185] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_186 : Valid inline_186 := by
  rw [eq_inline_186]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 3) valid_5
  subst c
  exact valid_inline_185

theorem eq_inline_187 : inline_187 = combine (5, 3) [placed 5 (3, 7) card_133, inline_186, placed 7 (6, 6) card_505] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_187 : Valid inline_187 := by
  rw [eq_inline_187]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_133
  rcases hc with rfl | hc
  · exact valid_inline_186
  subst c
  exact placed_valid 7 (6, 6) valid_505

theorem eq_card_529 : card_529 = combine (5, 6) [placed 4 (6, 2) card_12, placed 1 (3, 3) card_181, placed 4 (6, 2) card_189, placed 4 (6, 1) card_369, placed 1 (3, 3) card_474, placed 0 (4, 0) card_528, inline_187] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_529 : Valid card_529 := by
  rw [eq_card_529]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_474
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 0) valid_528
  subst c
  exact valid_inline_187

theorem eq_inline_188 : inline_188 = combine (2, 5) [placed 5 (2, 5) card_5, placed 0 (1, 2) card_20] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_188 : Valid inline_188 := by
  rw [eq_inline_188]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_5
  subst c
  exact placed_valid 0 (1, 2) valid_20

theorem eq_inline_189 : inline_189 = combine (3, 2) [placed 5 (0, 3) card_51, inline_188] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_189 : Valid inline_189 := by
  rw [eq_inline_189]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_51
  subst c
  exact valid_inline_188

theorem eq_inline_190 : inline_190 = combine (2, 2) [placed 6 (2, 5) card_23, inline_189] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_190 : Valid inline_190 := by
  rw [eq_inline_190]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 5) valid_23
  subst c
  exact valid_inline_189

theorem eq_card_530 : card_530 = combine (2, 4) [placed 2 (0, 5) card_72, placed 2 (0, 5) card_360, placed 0 (0, 1) card_499, inline_190] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_530 : Valid card_530 := by
  rw [eq_card_530]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_72
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_360
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_499
  subst c
  exact valid_inline_190

theorem eq_card_531 : card_531 = combine (1, 4) [placed 1 (0, 0) card_0, placed 0 (0, 0) card_530] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_531 : Valid card_531 := by
  rw [eq_card_531]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_530

theorem eq_inline_191 : inline_191 = combine (2, 6) [placed 4 (3, 2) card_19, placed 4 (3, 2) card_84, placed 3 (3, 3) card_314, placed 2 (1, 7) card_521] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_191 : Valid inline_191 := by
  rw [eq_inline_191]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_84
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 3) valid_314
  subst c
  exact placed_valid 2 (1, 7) valid_521

theorem eq_card_532 : card_532 = combine (2, 3) [placed 0 (2, 2) card_44, placed 0 (2, 2) card_52, placed 5 (0, 6) card_134, inline_191] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_532 : Valid card_532 := by
  rw [eq_card_532]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_134
  subst c
  exact valid_inline_191

theorem eq_inline_192 : inline_192 = combine (3, 4) [placed 0 (2, 0) card_53, placed 2 (1, 6) card_55, placed 7 (5, 4) card_392] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_192 : Valid inline_192 := by
  rw [eq_inline_192]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_55
  subst c
  exact placed_valid 7 (5, 4) valid_392

theorem eq_card_533 : card_533 = combine (4, 3) [placed 5 (0, 3) card_11, placed 0 (1, 0) card_279, inline_192] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_533 : Valid card_533 := by
  rw [eq_card_533]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_279
  subst c
  exact valid_inline_192

theorem eq_inline_193 : inline_193 = combine (2, 6) [placed 1 (2, 3) card_5, placed 1 (0, 3) card_177] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_193 : Valid inline_193 := by
  rw [eq_inline_193]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_5
  subst c
  exact placed_valid 1 (0, 3) valid_177

theorem eq_inline_194 : inline_194 = combine (3, 5) [placed 1 (2, 2) card_0, placed 7 (5, 6) card_239] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_194 : Valid inline_194 := by
  rw [eq_inline_194]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_0
  subst c
  exact placed_valid 7 (5, 6) valid_239

theorem eq_inline_195 : inline_195 = combine (3, 6) [placed 0 (2, 2) card_139, inline_193, inline_194] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_195 : Valid inline_195 := by
  rw [eq_inline_195]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_139
  rcases hc with rfl | hc
  · exact valid_inline_193
  subst c
  exact valid_inline_194

theorem eq_card_534 : card_534 = combine (2, 5) [placed 2 (2, 6) card_44, placed 2 (2, 6) card_52, placed 5 (0, 5) card_388, inline_195] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_534 : Valid card_534 := by
  rw [eq_card_534]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_388
  subst c
  exact valid_inline_195

theorem eq_card_535 : card_535 = combine (3, 5) [placed 2 (0, 7) card_345, placed 5 (0, 6) card_421, placed 2 (0, 7) card_522, placed 2 (1, 8) card_530, placed 0 (0, 0) card_532, placed 0 (0, 2) card_533, placed 2 (0, 8) card_534] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_535 : Valid card_535 := by
  rw [eq_card_535]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_345
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_421
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_522
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_530
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_532
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_533
  subst c
  exact placed_valid 2 (0, 8) valid_534

theorem eq_card_536 : card_536 = combine (3, 5) [placed 4 (4, 1) card_14, placed 7 (6, 6) card_88, placed 3 (6, 2) card_213, placed 5 (0, 6) card_534] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_536 : Valid card_536 := by
  rw [eq_card_536]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_88
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_213
  subst c
  exact placed_valid 5 (0, 6) valid_534

theorem eq_inline_196 : inline_196 = combine (3, 3) [placed 6 (4, 5) card_45, placed 0 (1, 2) card_418] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_196 : Valid inline_196 := by
  rw [eq_inline_196]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_45
  subst c
  exact placed_valid 0 (1, 2) valid_418

theorem eq_inline_197 : inline_197 = combine (2, 5) [placed 6 (2, 6) card_15, placed 0 (1, 2) card_425] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_197 : Valid inline_197 := by
  rw [eq_inline_197]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_15
  subst c
  exact placed_valid 0 (1, 2) valid_425

theorem eq_inline_198 : inline_198 = combine (2, 5) [placed 1 (2, 2) card_0, placed 4 (2, 2) card_23] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_198 : Valid inline_198 := by
  rw [eq_inline_198]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_0
  subst c
  exact placed_valid 4 (2, 2) valid_23

theorem eq_inline_199 : inline_199 = combine (3, 5) [placed 3 (4, 2) card_0, inline_198] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_199 : Valid inline_199 := by
  rw [eq_inline_199]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 2) valid_0
  subst c
  exact valid_inline_198

theorem eq_inline_200 : inline_200 = combine (3, 6) [placed 4 (4, 2) card_139, placed 0 (1, 2) card_382, inline_199] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_200 : Valid inline_200 := by
  rw [eq_inline_200]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_139
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_382
  subst c
  exact valid_inline_199

theorem eq_inline_201 : inline_201 = combine (4, 4) [placed 4 (5, 1) card_13, placed 5 (1, 4) card_30, inline_200] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_201 : Valid inline_201 := by
  rw [eq_inline_201]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_30
  subst c
  exact valid_inline_200

theorem eq_inline_202 : inline_202 = combine (4, 5) [placed 0 (1, 1) card_166, placed 2 (1, 7) card_464, inline_197, inline_201] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_202 : Valid inline_202 := by
  rw [eq_inline_202]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_166
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_464
  rcases hc with rfl | hc
  · exact valid_inline_197
  subst c
  exact valid_inline_201

theorem eq_card_537 : card_537 = combine (4, 3) [placed 1 (1, 3) card_74, placed 0 (0, 1) card_108, inline_196, inline_202] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_537 : Valid card_537 := by
  rw [eq_card_537]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_74
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_108
  rcases hc with rfl | hc
  · exact valid_inline_196
  subst c
  exact valid_inline_202

theorem eq_inline_203 : inline_203 = combine (5, 7) [placed 0 (3, 3) card_190, placed 4 (7, 3) card_190, placed 3 (8, 5) card_258, placed 2 (1, 9) card_273, placed 0 (1, 4) card_415, placed 1 (2, 4) card_507] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_203 : Valid inline_203 := by
  rw [eq_inline_203]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_258
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 9) valid_273
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 4) valid_415
  subst c
  exact placed_valid 1 (2, 4) valid_507

theorem eq_inline_204 : inline_204 = combine (4, 6) [placed 2 (1, 6) card_2, placed 2 (3, 9) card_512] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_204 : Valid inline_204 := by
  rw [eq_inline_204]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_2
  subst c
  exact placed_valid 2 (3, 9) valid_512

theorem eq_inline_205 : inline_205 = combine (5, 7) [placed 0 (5, 3) card_7, placed 4 (6, 3) card_9, placed 3 (6, 4) card_354] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_205 : Valid inline_205 := by
  rw [eq_inline_205]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_9
  subst c
  exact placed_valid 3 (6, 4) valid_354

theorem eq_inline_206 : inline_206 = combine (4, 6) [placed 2 (1, 6) card_2, placed 4 (5, 3) card_15] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_206 : Valid inline_206 := by
  rw [eq_inline_206]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_2
  subst c
  exact placed_valid 4 (5, 3) valid_15

theorem eq_inline_207 : inline_207 = combine (5, 7) [placed 1 (4, 4) card_8, placed 7 (6, 7) card_505] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_207 : Valid inline_207 := by
  rw [eq_inline_207]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_8
  subst c
  exact placed_valid 7 (6, 7) valid_505

theorem eq_inline_208 : inline_208 = combine (5, 4) [placed 2 (3, 7) card_136, inline_205, inline_206, inline_207] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_208 : Valid inline_208 := by
  rw [eq_inline_208]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_136
  rcases hc with rfl | hc
  · exact valid_inline_205
  rcases hc with rfl | hc
  · exact valid_inline_206
  subst c
  exact valid_inline_207

theorem eq_inline_209 : inline_209 = combine (4, 6) [placed 2 (1, 6) card_2, placed 0 (3, 2) card_517] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_209 : Valid inline_209 := by
  rw [eq_inline_209]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_2
  subst c
  exact placed_valid 0 (3, 2) valid_517

theorem eq_inline_210 : inline_210 = combine (5, 7) [placed 5 (2, 8) card_116, placed 3 (7, 4) card_180, placed 3 (8, 5) card_258, placed 2 (1, 9) card_273, placed 1 (3, 4) card_275, placed 0 (1, 4) card_415, placed 4 (8, 2) card_518] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_210 : Valid inline_210 := by
  rw [eq_inline_210]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_258
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 9) valid_273
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_275
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 4) valid_415
  subst c
  exact placed_valid 4 (8, 2) valid_518

theorem eq_inline_211 : inline_211 = combine (4, 6) [placed 2 (1, 6) card_2, placed 2 (3, 9) card_527] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_211 : Valid inline_211 := by
  rw [eq_inline_211]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_2
  subst c
  exact placed_valid 2 (3, 9) valid_527

theorem eq_inline_212 : inline_212 = combine (4, 6) [placed 2 (1, 6) card_2, placed 2 (3, 9) card_537] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_212 : Valid inline_212 := by
  rw [eq_inline_212]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_2
  subst c
  exact placed_valid 2 (3, 9) valid_537

theorem eq_card_538 : card_538 = combine (5, 6) [placed 0 (4, 1) card_459, inline_203, inline_204, inline_208, inline_209, inline_210, inline_211, placed 0 (0, 1) card_529, placed 2 (3, 10) card_535, inline_212] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_538 : Valid card_538 := by
  rw [eq_card_538]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_459
  rcases hc with rfl | hc
  · exact valid_inline_203
  rcases hc with rfl | hc
  · exact valid_inline_204
  rcases hc with rfl | hc
  · exact valid_inline_208
  rcases hc with rfl | hc
  · exact valid_inline_209
  rcases hc with rfl | hc
  · exact valid_inline_210
  rcases hc with rfl | hc
  · exact valid_inline_211
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_529
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 10) valid_535
  subst c
  exact valid_inline_212

theorem eq_inline_213 : inline_213 = combine (3, 5) [placed 2 (0, 5) card_5, placed 2 (3, 5) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_213 : Valid inline_213 := by
  rw [eq_inline_213]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_5
  subst c
  exact placed_valid 2 (3, 5) valid_6

theorem eq_inline_214 : inline_214 = combine (3, 4) [placed 7 (3, 4) card_5, inline_213] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_214 : Valid inline_214 := by
  rw [eq_inline_214]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 4) valid_5
  subst c
  exact valid_inline_213

theorem eq_inline_215 : inline_215 = combine (4, 2) [placed 0 (0, 1) card_1, placed 4 (4, 2) card_153] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_215 : Valid inline_215 := by
  rw [eq_inline_215]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_1
  subst c
  exact placed_valid 4 (4, 2) valid_153

theorem eq_inline_216 : inline_216 = combine (3, 5) [placed 2 (0, 5) card_5, inline_215] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_216 : Valid inline_216 := by
  rw [eq_inline_216]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_5
  subst c
  exact valid_inline_215

theorem eq_inline_217 : inline_217 = combine (3, 4) [placed 7 (3, 4) card_5, inline_216] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_217 : Valid inline_217 := by
  rw [eq_inline_217]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 4) valid_5
  subst c
  exact valid_inline_216

theorem eq_inline_218 : inline_218 = combine (1, 2) [placed 4 (4, 1) card_0, placed 7 (1, 5) card_2] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_218 : Valid inline_218 := by
  rw [eq_inline_218]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 7 (1, 5) valid_2

theorem eq_inline_219 : inline_219 = combine (1, 1) [placed 0 (0, 1) card_5, inline_218] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_219 : Valid inline_219 := by
  rw [eq_inline_219]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_218

theorem eq_inline_220 : inline_220 = combine (4, 1) [placed 0 (2, 0) card_83, placed 3 (4, 1) card_281] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_220 : Valid inline_220 := by
  rw [eq_inline_220]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_83
  subst c
  exact placed_valid 3 (4, 1) valid_281

theorem eq_inline_221 : inline_221 = combine (2, 1) [inline_214, inline_217, inline_219, inline_220] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_221 : Valid inline_221 := by
  rw [eq_inline_221]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_214
  rcases hc with rfl | hc
  · exact valid_inline_217
  rcases hc with rfl | hc
  · exact valid_inline_219
  subst c
  exact valid_inline_220

theorem eq_inline_222 : inline_222 = combine (2, 5) [placed 5 (1, 9) card_4, inline_221] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_222 : Valid inline_222 := by
  rw [eq_inline_222]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 9) valid_4
  subst c
  exact valid_inline_221

theorem eq_inline_223 : inline_223 = combine (0, 5) [placed 7 (1, 8) card_5, inline_222] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_223 : Valid inline_223 := by
  rw [eq_inline_223]
  apply combination_rule (0, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 8) valid_5
  subst c
  exact valid_inline_222

theorem eq_card_539 : card_539 = combine (1, 9) [placed 0 (1, 5) card_6, inline_223] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_539 : Valid card_539 := by
  rw [eq_card_539]
  apply combination_rule (1, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 5) valid_6
  subst c
  exact valid_inline_223

theorem eq_inline_224 : inline_224 = combine (2, 3) [placed 1 (1, 2) card_237, placed 3 (4, 3) card_281] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_224 : Valid inline_224 := by
  rw [eq_inline_224]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_237
  subst c
  exact placed_valid 3 (4, 3) valid_281

theorem eq_inline_225 : inline_225 = combine (4, 4) [placed 5 (1, 5) card_164, placed 2 (3, 7) card_199, placed 0 (0, 1) card_283] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_225 : Valid inline_225 := by
  rw [eq_inline_225]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_164
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_199
  subst c
  exact placed_valid 0 (0, 1) valid_283

theorem eq_inline_226 : inline_226 = combine (4, 5) [placed 0 (0, 3) card_170, inline_225] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_226 : Valid inline_226 := by
  rw [eq_inline_226]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_170
  subst c
  exact valid_inline_225

theorem eq_inline_227 : inline_227 = combine (0, 6) [placed 4 (1, 6) card_16, inline_226] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_227 : Valid inline_227 := by
  rw [eq_inline_227]
  apply combination_rule (0, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 6) valid_16
  subst c
  exact valid_inline_226

theorem eq_card_540 : card_540 = combine (4, 3) [placed 2 (3, 6) card_44, inline_224, inline_227] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_540 : Valid card_540 := by
  rw [eq_card_540]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_44
  rcases hc with rfl | hc
  · exact valid_inline_224
  subst c
  exact valid_inline_227

theorem eq_inline_228 : inline_228 = combine (4, 2) [placed 5 (3, 6) card_0, placed 7 (4, 4) card_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_228 : Valid inline_228 := by
  rw [eq_inline_228]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_0
  subst c
  exact placed_valid 7 (4, 4) valid_35

theorem eq_inline_229 : inline_229 = combine (4, 3) [placed 0 (0, 1) card_170, inline_228] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_229 : Valid inline_229 := by
  rw [eq_inline_229]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_170
  subst c
  exact valid_inline_228

theorem eq_inline_230 : inline_230 = combine (3, 4) [placed 2 (3, 5) card_6, placed 0 (0, 0) card_86, inline_229] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_230 : Valid inline_230 := by
  rw [eq_inline_230]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_86
  subst c
  exact valid_inline_229

theorem eq_inline_231 : inline_231 = combine (3, 5) [placed 6 (4, 5) card_0, inline_230] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_231 : Valid inline_231 := by
  rw [eq_inline_231]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_0
  subst c
  exact valid_inline_230

theorem eq_inline_232 : inline_232 = combine (2, 5) [placed 5 (1, 9) card_4, inline_231] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_232 : Valid inline_232 := by
  rw [eq_inline_232]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 9) valid_4
  subst c
  exact valid_inline_231

theorem eq_inline_233 : inline_233 = combine (0, 4) [placed 7 (1, 8) card_4, inline_232] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_233 : Valid inline_233 := by
  rw [eq_inline_233]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 8) valid_4
  subst c
  exact valid_inline_232

theorem eq_inline_234 : inline_234 = combine (1, 9) [placed 0 (1, 5) card_6, inline_233] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_234 : Valid inline_234 := by
  rw [eq_inline_234]
  apply combination_rule (1, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 5) valid_6
  subst c
  exact valid_inline_233

theorem eq_card_541 : card_541 = combine (1, 8) [placed 4 (1, 4) card_6, inline_234] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_541 : Valid card_541 := by
  rw [eq_card_541]
  apply combination_rule (1, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 4) valid_6
  subst c
  exact valid_inline_234

theorem eq_inline_235 : inline_235 = combine (5, 2) [placed 6 (6, 2) card_0, placed 2 (1, 3) card_1] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_235 : Valid inline_235 := by
  rw [eq_inline_235]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 2) valid_0
  subst c
  exact placed_valid 2 (1, 3) valid_1

theorem eq_inline_236 : inline_236 = combine (4, 3) [placed 0 (3, 1) card_29, inline_235] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_236 : Valid inline_236 := by
  rw [eq_inline_236]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_29
  subst c
  exact valid_inline_235

theorem eq_inline_237 : inline_237 = combine (4, 2) [placed 0 (0, 1) card_1, inline_236] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_237 : Valid inline_237 := by
  rw [eq_inline_237]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_1
  subst c
  exact valid_inline_236

theorem eq_inline_238 : inline_238 = combine (2, 1) [placed 7 (3, 4) card_5, inline_237] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_238 : Valid inline_238 := by
  rw [eq_inline_238]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 4) valid_5
  subst c
  exact valid_inline_237

theorem eq_card_542 : card_542 = combine (1, 3) [placed 7 (1, 5) card_3, inline_238] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_542 : Valid card_542 := by
  rw [eq_card_542]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_3
  subst c
  exact valid_inline_238

theorem eq_inline_239 : inline_239 = combine (5, 7) [placed 0 (4, 3) card_261, placed 1 (1, 6) card_370] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_239 : Valid inline_239 := by
  rw [eq_inline_239]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_261
  subst c
  exact placed_valid 1 (1, 6) valid_370

theorem eq_inline_240 : inline_240 = combine (5, 5) [placed 0 (4, 3) card_154, placed 0 (1, 3) card_170] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_240 : Valid inline_240 := by
  rw [eq_inline_240]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_154
  subst c
  exact placed_valid 0 (1, 3) valid_170

theorem eq_inline_241 : inline_241 = combine (5, 7) [placed 6 (5, 7) card_1, inline_240] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_241 : Valid inline_241 := by
  rw [eq_inline_241]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_1
  subst c
  exact valid_inline_240

theorem eq_inline_242 : inline_242 = combine (3, 7) [placed 0 (2, 7) card_16, inline_241] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_242 : Valid inline_242 := by
  rw [eq_inline_242]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 7) valid_16
  subst c
  exact valid_inline_241

theorem eq_inline_243 : inline_243 = combine (1, 6) [placed 7 (2, 10) card_4, inline_242] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_243 : Valid inline_243 := by
  rw [eq_inline_243]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 10) valid_4
  subst c
  exact valid_inline_242

theorem eq_inline_244 : inline_244 = combine (2, 10) [placed 4 (2, 6) card_6, inline_243] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_244 : Valid inline_244 := by
  rw [eq_inline_244]
  apply combination_rule (2, 10) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 6) valid_6
  subst c
  exact valid_inline_243

theorem eq_inline_245 : inline_245 = combine (2, 10) [placed 4 (2, 6) card_6, placed 0 (1, 2) card_539] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_245 : Valid inline_245 := by
  rw [eq_inline_245]
  apply combination_rule (2, 10) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 6) valid_6
  subst c
  exact placed_valid 0 (1, 2) valid_539

theorem eq_inline_246 : inline_246 = combine (4, 6) [placed 0 (4, 2) card_7, placed 0 (1, 2) card_86, placed 0 (1, 2) card_542] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_246 : Valid inline_246 := by
  rw [eq_inline_246]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_86
  subst c
  exact placed_valid 0 (1, 2) valid_542

theorem eq_inline_247 : inline_247 = combine (4, 5) [placed 0 (1, 2) card_433, inline_239, inline_244, inline_245, placed 0 (1, 0) card_540, placed 0 (1, 2) card_541, inline_246] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_247 : Valid inline_247 := by
  rw [eq_inline_247]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_433
  rcases hc with rfl | hc
  · exact valid_inline_239
  rcases hc with rfl | hc
  · exact valid_inline_244
  rcases hc with rfl | hc
  · exact valid_inline_245
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_540
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_541
  subst c
  exact valid_inline_246

theorem eq_inline_248 : inline_248 = combine (2, 5) [placed 7 (2, 7) card_3, placed 1 (2, 5) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_248 : Valid inline_248 := by
  rw [eq_inline_248]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 7) valid_3
  subst c
  exact placed_valid 1 (2, 5) valid_5

theorem eq_inline_249 : inline_249 = combine (3, 8) [placed 1 (0, 6) card_278, inline_248] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_249 : Valid inline_249 := by
  rw [eq_inline_249]
  apply combination_rule (3, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 6) valid_278
  subst c
  exact valid_inline_248

theorem eq_card_543 : card_543 = combine (2, 9) [placed 1 (1, 6) card_8, placed 0 (1, 3) card_280, inline_247, inline_249] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_543 : Valid card_543 := by
  rw [eq_card_543]
  apply combination_rule (2, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 6) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_280
  rcases hc with rfl | hc
  · exact valid_inline_247
  subst c
  exact valid_inline_249

theorem eq_inline_250 : inline_250 = combine (5, 3) [placed 4 (6, 3) card_0, placed 7 (6, 4) card_62] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_250 : Valid inline_250 := by
  rw [eq_inline_250]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_0
  subst c
  exact placed_valid 7 (6, 4) valid_62

theorem eq_inline_251 : inline_251 = combine (4, 3) [placed 3 (5, 3) card_15, placed 1 (0, 2) card_259, inline_250] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_251 : Valid inline_251 := by
  rw [eq_inline_251]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_259
  subst c
  exact valid_inline_250

theorem eq_card_544 : card_544 = combine (3, 4) [placed 2 (2, 5) card_23, inline_251] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_544 : Valid card_544 := by
  rw [eq_card_544]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 5) valid_23
  subst c
  exact valid_inline_251

theorem eq_inline_252 : inline_252 = combine (1, 6) [placed 4 (2, 2) card_19, placed 4 (2, 2) card_84, placed 3 (2, 3) card_314, placed 2 (0, 7) card_419] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_252 : Valid inline_252 := by
  rw [eq_inline_252]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_84
  rcases hc with rfl | hc
  · exact placed_valid 3 (2, 3) valid_314
  subst c
  exact placed_valid 2 (0, 7) valid_419

theorem eq_card_545 : card_545 = combine (1, 3) [placed 2 (1, 6) card_27, placed 0 (1, 2) card_52, placed 6 (2, 9) card_284, inline_252] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_545 : Valid card_545 := by
  rw [eq_card_545]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 9) valid_284
  subst c
  exact valid_inline_252

theorem eq_inline_253 : inline_253 = combine (3, 6) [placed 2 (0, 7) card_25, placed 5 (0, 6) card_27, placed 1 (0, 5) card_37] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_253 : Valid inline_253 := by
  rw [eq_inline_253]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_25
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_27
  subst c
  exact placed_valid 1 (0, 5) valid_37

theorem eq_inline_254 : inline_254 = combine (0, 6) [placed 3 (1, 3) card_5, inline_253] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_254 : Valid inline_254 := by
  rw [eq_inline_254]
  apply combination_rule (0, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 3) valid_5
  subst c
  exact valid_inline_253

theorem eq_inline_255 : inline_255 = combine (2, 6) [placed 1 (1, 3) card_5, inline_254] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_255 : Valid inline_255 := by
  rw [eq_inline_255]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_5
  subst c
  exact valid_inline_254

theorem eq_inline_256 : inline_256 = combine (2, 3) [placed 5 (1, 6) card_5, inline_255] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_256 : Valid inline_256 := by
  rw [eq_inline_256]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_5
  subst c
  exact valid_inline_255

theorem eq_inline_257 : inline_257 = combine (1, 3) [placed 2 (0, 7) card_19, placed 6 (2, 7) card_19, placed 2 (0, 7) card_62, inline_256] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_257 : Valid inline_257 := by
  rw [eq_inline_257]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 7) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_62
  subst c
  exact valid_inline_256

theorem eq_card_546 : card_546 = combine (1, 6) [placed 4 (2, 3) card_10, placed 2 (1, 7) card_44, placed 4 (2, 3) card_63, inline_257] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_546 : Valid card_546 := by
  rw [eq_card_546]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 3) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 3) valid_63
  subst c
  exact valid_inline_257

theorem eq_inline_258 : inline_258 = combine (1, 5) [placed 6 (1, 5) card_6, placed 4 (2, 2) card_17] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_258 : Valid inline_258 := by
  rw [eq_inline_258]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 5) valid_6
  subst c
  exact placed_valid 4 (2, 2) valid_17

theorem eq_inline_259 : inline_259 = combine (2, 4) [placed 1 (1, 1) card_5, placed 5 (0, 4) card_525] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_259 : Valid inline_259 := by
  rw [eq_inline_259]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact placed_valid 5 (0, 4) valid_525

theorem eq_card_547 : card_547 = combine (1, 4) [placed 0 (0, 0) card_19, placed 3 (2, 1) card_314, inline_258, inline_259] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_547 : Valid card_547 := by
  rw [eq_card_547]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 3 (2, 1) valid_314
  rcases hc with rfl | hc
  · exact valid_inline_258
  subst c
  exact valid_inline_259

theorem eq_card_548 : card_548 = combine (1, 7) [placed 4 (2, 4) card_10, placed 2 (1, 8) card_52, placed 0 (0, 3) card_189, placed 2 (0, 8) card_547] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_548 : Valid card_548 := by
  rw [eq_card_548]
  apply combination_rule (1, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 4) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_189
  subst c
  exact placed_valid 2 (0, 8) valid_547

theorem eq_card_549 : card_549 = combine (1, 3) [placed 6 (2, 6) card_10, placed 0 (1, 2) card_52, placed 2 (0, 6) card_63, placed 0 (0, 2) card_547] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_549 : Valid card_549 := by
  rw [eq_card_549]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_63
  subst c
  exact placed_valid 0 (0, 2) valid_547

theorem eq_card_550 : card_550 = combine (5, 6) [placed 5 (0, 6) card_390, placed 3 (8, 3) card_544, placed 6 (6, 10) card_545, placed 4 (6, 1) card_546, placed 4 (6, 0) card_548] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_550 : Valid card_550 := by
  rw [eq_card_550]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_390
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_544
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 10) valid_545
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_546
  subst c
  exact placed_valid 4 (6, 0) valid_548

theorem eq_inline_260 : inline_260 = combine (3, 3) [placed 7 (7, 3) card_6, placed 4 (4, 2) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_260 : Valid inline_260 := by
  rw [eq_inline_260]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 3) valid_6
  subst c
  exact placed_valid 4 (4, 2) valid_78

theorem eq_inline_261 : inline_261 = combine (3, 3) [placed 0 (2, 3) card_4, placed 7 (5, 3) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_261 : Valid inline_261 := by
  rw [eq_inline_261]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_4
  subst c
  exact placed_valid 7 (5, 3) valid_6

theorem eq_inline_262 : inline_262 = combine (4, 3) [placed 4 (7, 2) card_25, inline_260, inline_261] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_262 : Valid inline_262 := by
  rw [eq_inline_262]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_25
  rcases hc with rfl | hc
  · exact valid_inline_260
  subst c
  exact valid_inline_261

theorem eq_inline_263 : inline_263 = combine (7, 3) [placed 5 (6, 6) card_5, inline_262] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_263 : Valid inline_263 := by
  rw [eq_inline_263]
  apply combination_rule (7, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (6, 6) valid_5
  subst c
  exact valid_inline_262

theorem eq_inline_264 : inline_264 = combine (5, 3) [placed 7 (6, 6) card_5, inline_263] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_264 : Valid inline_264 := by
  rw [eq_inline_264]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_5
  subst c
  exact valid_inline_263

theorem eq_inline_265 : inline_265 = combine (2, 5) [placed 0 (2, 5) card_1, inline_264] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_265 : Valid inline_265 := by
  rw [eq_inline_265]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_1
  subst c
  exact valid_inline_264

theorem eq_inline_266 : inline_266 = combine (5, 6) [placed 3 (6, 3) card_5, inline_265] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_266 : Valid inline_266 := by
  rw [eq_inline_266]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_5
  subst c
  exact valid_inline_265

theorem eq_inline_267 : inline_267 = combine (6, 6) [placed 0 (5, 2) card_19, placed 0 (5, 2) card_84, placed 1 (5, 3) card_314, inline_266] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_267 : Valid inline_267 := by
  rw [eq_inline_267]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 2) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 2) valid_84
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 3) valid_314
  subst c
  exact valid_inline_266

theorem eq_inline_268 : inline_268 = combine (6, 3) [placed 2 (5, 6) card_10, placed 4 (6, 2) card_44, placed 2 (5, 6) card_63, inline_267] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_268 : Valid inline_268 := by
  rw [eq_inline_268]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 6) valid_63
  subst c
  exact valid_inline_267

theorem eq_card_551 : card_551 = combine (6, 4) [placed 5 (3, 5) card_52, placed 0 (3, 1) card_523, inline_268] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_551 : Valid card_551 := by
  rw [eq_card_551]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_523
  subst c
  exact valid_inline_268

theorem eq_inline_269 : inline_269 = combine (5, 6) [placed 4 (7, 6) card_3, placed 1 (5, 6) card_389] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_269 : Valid inline_269 := by
  rw [eq_inline_269]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 6) valid_3
  subst c
  exact placed_valid 1 (5, 6) valid_389

theorem eq_inline_270 : inline_270 = combine (7, 7) [placed 1 (4, 4) card_544, placed 2 (6, 11) card_545, placed 0 (6, 2) card_546, inline_269, placed 0 (6, 1) card_548] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_270 : Valid inline_270 := by
  rw [eq_inline_270]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_544
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 11) valid_545
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 2) valid_546
  rcases hc with rfl | hc
  · exact valid_inline_269
  subst c
  exact placed_valid 0 (6, 1) valid_548

theorem eq_card_552 : card_552 = combine (8, 6) [placed 1 (4, 4) card_188, placed 0 (6, 3) card_258, placed 2 (3, 10) card_326, placed 5 (0, 8) card_543, inline_270, placed 0 (2, 1) card_551] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_552 : Valid card_552 := by
  rw [eq_card_552]
  apply combination_rule (8, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 3) valid_258
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 10) valid_326
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 8) valid_543
  rcases hc with rfl | hc
  · exact valid_inline_270
  subst c
  exact placed_valid 0 (2, 1) valid_551

theorem eq_inline_271 : inline_271 = combine (5, 7) [placed 2 (3, 7) card_3, placed 7 (5, 7) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_271 : Valid inline_271 := by
  rw [eq_inline_271]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_3
  subst c
  exact placed_valid 7 (5, 7) valid_5

theorem eq_inline_272 : inline_272 = combine (5, 5) [placed 6 (6, 7) card_10, placed 6 (5, 7) card_52, placed 0 (5, 3) card_52, inline_271] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_272 : Valid inline_272 := by
  rw [eq_inline_272]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 7) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_52
  subst c
  exact valid_inline_271

theorem eq_inline_273 : inline_273 = combine (5, 6) [placed 4 (7, 6) card_3, inline_272] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_273 : Valid inline_273 := by
  rw [eq_inline_273]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 6) valid_3
  subst c
  exact valid_inline_272

theorem eq_inline_274 : inline_274 = combine (6, 4) [placed 7 (7, 4) card_6, placed 0 (4, 3) card_145] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_274 : Valid inline_274 := by
  rw [eq_inline_274]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 4) valid_6
  subst c
  exact placed_valid 0 (4, 3) valid_145

theorem eq_inline_275 : inline_275 = combine (7, 4) [placed 4 (7, 3) card_54, placed 5 (2, 4) card_158, inline_274] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_275 : Valid inline_275 := by
  rw [eq_inline_275]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_158
  subst c
  exact valid_inline_274

theorem eq_inline_276 : inline_276 = combine (6, 7) [placed 2 (3, 7) card_2, inline_275] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_276 : Valid inline_276 := by
  rw [eq_inline_276]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_2
  subst c
  exact valid_inline_275

theorem eq_inline_277 : inline_277 = combine (4, 3) [placed 6 (5, 7) card_54, placed 5 (2, 7) card_247] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_277 : Valid inline_277 := by
  rw [eq_inline_277]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_54
  subst c
  exact placed_valid 5 (2, 7) valid_247

theorem eq_inline_278 : inline_278 = combine (5, 6) [placed 4 (7, 6) card_3, inline_277] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_278 : Valid inline_278 := by
  rw [eq_inline_278]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 6) valid_3
  subst c
  exact valid_inline_277

theorem eq_inline_279 : inline_279 = combine (5, 4) [placed 5 (2, 7) card_433, inline_273, inline_276, inline_278] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_279 : Valid inline_279 := by
  rw [eq_inline_279]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_433
  rcases hc with rfl | hc
  · exact valid_inline_273
  rcases hc with rfl | hc
  · exact valid_inline_276
  subst c
  exact valid_inline_278

theorem eq_card_553 : card_553 = combine (7, 6) [placed 5 (3, 7) card_107, placed 5 (3, 7) card_163, placed 0 (2, 1) card_538, placed 0 (0, 0) card_552, inline_279] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_553 : Valid card_553 := by
  rw [eq_card_553]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_107
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_163
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_538
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_552
  subst c
  exact valid_inline_279

theorem eq_inline_280 : inline_280 = combine (1, 3) [placed 1 (0, 0) card_0, placed 0 (0, 3) card_515] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_280 : Valid inline_280 := by
  rw [eq_inline_280]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 0 (0, 3) valid_515

theorem eq_card_554 : card_554 = combine (1, 4) [placed 1 (0, 1) card_5, inline_280] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_554 : Valid card_554 := by
  rw [eq_card_554]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_5
  subst c
  exact valid_inline_280

theorem eq_inline_281 : inline_281 = combine (2, 2) [placed 6 (3, 6) card_61, placed 0 (2, 2) card_194, placed 0 (0, 1) card_224] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_281 : Valid inline_281 := by
  rw [eq_inline_281]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_61
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_194
  subst c
  exact placed_valid 0 (0, 1) valid_224

theorem eq_card_555 : card_555 = combine (3, 3) [placed 6 (4, 7) card_13, placed 4 (4, 1) card_14, placed 0 (2, 1) card_31, placed 7 (5, 6) card_230, placed 0 (2, 1) card_367, placed 0 (2, 2) card_428, inline_281] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_555 : Valid card_555 := by
  rw [eq_card_555]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_230
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_367
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_428
  subst c
  exact valid_inline_281

theorem eq_inline_282 : inline_282 = combine (5, 4) [placed 2 (2, 7) card_115, placed 2 (2, 7) card_171, placed 2 (2, 5) card_197, placed 0 (2, 3) card_197, placed 2 (2, 7) card_285] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_282 : Valid inline_282 := by
  rw [eq_inline_282]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_171
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 5) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_197
  subst c
  exact placed_valid 2 (2, 7) valid_285

theorem eq_card_556 : card_556 = combine (2, 4) [placed 6 (4, 4) card_3, inline_282] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_556 : Valid card_556 := by
  rw [eq_card_556]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_3
  subst c
  exact valid_inline_282

theorem eq_inline_283 : inline_283 = combine (4, 7) [placed 6 (5, 9) card_13, placed 7 (5, 7) card_28, placed 2 (1, 8) card_58] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_283 : Valid inline_283 := by
  rw [eq_inline_283]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 9) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 7) valid_28
  subst c
  exact placed_valid 2 (1, 8) valid_58

theorem eq_inline_284 : inline_284 = combine (1, 5) [placed 5 (1, 6) card_2, placed 6 (4, 6) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_284 : Valid inline_284 := by
  rw [eq_inline_284]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_2
  subst c
  exact placed_valid 6 (4, 6) valid_5

theorem eq_inline_285 : inline_285 = combine (3, 4) [placed 7 (3, 6) card_1, placed 7 (5, 4) card_392] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_285 : Valid inline_285 := by
  rw [eq_inline_285]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 6) valid_1
  subst c
  exact placed_valid 7 (5, 4) valid_392

theorem eq_inline_286 : inline_286 = combine (3, 3) [placed 5 (0, 3) card_11, placed 1 (1, 2) card_41, inline_285] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_286 : Valid inline_286 := by
  rw [eq_inline_286]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_41
  subst c
  exact valid_inline_285

theorem eq_inline_287 : inline_287 = combine (2, 2) [inline_284, inline_286] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_287 : Valid inline_287 := by
  rw [eq_inline_287]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_284
  subst c
  exact valid_inline_286

theorem eq_inline_288 : inline_288 = combine (4, 3) [placed 2 (3, 7) card_42, placed 1 (1, 2) card_152, inline_287] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_288 : Valid inline_288 := by
  rw [eq_inline_288]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_42
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_152
  subst c
  exact valid_inline_287

theorem eq_inline_289 : inline_289 = combine (3, 6) [placed 2 (1, 6) card_5, inline_288] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_289 : Valid inline_289 := by
  rw [eq_inline_289]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_5
  subst c
  exact valid_inline_288

theorem eq_card_557 : card_557 = combine (4, 6) [placed 0 (1, 3) card_110, placed 0 (1, 3) card_119, placed 0 (1, 2) card_430, placed 0 (1, 4) card_461, placed 0 (1, 1) card_555, inline_283, inline_289] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_557 : Valid card_557 := by
  rw [eq_card_557]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_110
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_119
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_430
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 4) valid_461
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_555
  rcases hc with rfl | hc
  · exact valid_inline_283
  subst c
  exact valid_inline_289

theorem eq_inline_290 : inline_290 = combine (3, 1) [placed 2 (0, 2) card_5, placed 0 (0, 0) card_471] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_290 : Valid inline_290 := by
  rw [eq_inline_290]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_471

theorem eq_card_558 : card_558 = combine (3, 2) [placed 0 (0, 1) card_8, placed 1 (0, 2) card_16, placed 2 (0, 3) card_24, inline_290] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_558 : Valid card_558 := by
  rw [eq_card_558]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_16
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_24
  subst c
  exact valid_inline_290

theorem eq_inline_291 : inline_291 = combine (4, 0) [placed 5 (3, 4) card_0, placed 1 (3, 0) card_17] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_291 : Valid inline_291 := by
  rw [eq_inline_291]
  apply combination_rule (4, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_0
  subst c
  exact placed_valid 1 (3, 0) valid_17

theorem eq_inline_292 : inline_292 = combine (1, 3) [placed 6 (4, 3) card_0, placed 0 (0, 3) card_0] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_292 : Valid inline_292 := by
  rw [eq_inline_292]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_0
  subst c
  exact placed_valid 0 (0, 3) valid_0

theorem eq_inline_293 : inline_293 = combine (2, 3) [placed 6 (6, 4) card_1, inline_292] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_293 : Valid inline_293 := by
  rw [eq_inline_293]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 4) valid_1
  subst c
  exact valid_inline_292

theorem eq_inline_294 : inline_294 = combine (4, 4) [placed 1 (3, 1) card_5, inline_293] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_294 : Valid inline_294 := by
  rw [eq_inline_294]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 1) valid_5
  subst c
  exact valid_inline_293

theorem eq_inline_295 : inline_295 = combine (6, 4) [placed 0 (3, 0) card_35, inline_294] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_295 : Valid inline_295 := by
  rw [eq_inline_295]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_35
  subst c
  exact valid_inline_294

theorem eq_inline_296 : inline_296 = combine (5, 0) [placed 3 (6, 0) card_244, inline_295] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_296 : Valid inline_296 := by
  rw [eq_inline_296]
  apply combination_rule (5, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 0) valid_244
  subst c
  exact valid_inline_295

theorem eq_inline_297 : inline_297 = combine (3, 4) [placed 5 (3, 4) card_5, inline_296] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_297 : Valid inline_297 := by
  rw [eq_inline_297]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_5
  subst c
  exact valid_inline_296

theorem eq_card_559 : card_559 = combine (6, 1) [placed 2 (3, 2) card_8, placed 3 (7, 0) card_236, inline_291, inline_297] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_559 : Valid card_559 := by
  rw [eq_card_559]
  apply combination_rule (6, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 0) valid_236
  rcases hc with rfl | hc
  · exact valid_inline_291
  subst c
  exact valid_inline_297

theorem eq_inline_298 : inline_298 = combine (5, 2) [placed 1 (2, 1) card_44, placed 2 (3, 5) card_156] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_298 : Valid inline_298 := by
  rw [eq_inline_298]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 1) valid_44
  subst c
  exact placed_valid 2 (3, 5) valid_156

theorem eq_inline_299 : inline_299 = combine (5, 1) [placed 3 (6, 1) card_44, placed 3 (6, 1) card_52, inline_298] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_299 : Valid inline_299 := by
  rw [eq_inline_299]
  apply combination_rule (5, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 1) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 1) valid_52
  subst c
  exact valid_inline_298

theorem eq_inline_300 : inline_300 = combine (4, 1) [placed 5 (3, 4) card_5, inline_299] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_300 : Valid inline_300 := by
  rw [eq_inline_300]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_5
  subst c
  exact valid_inline_299

theorem eq_inline_301 : inline_301 = combine (6, 5) [placed 7 (6, 5) card_153, inline_300] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_301 : Valid inline_301 := by
  rw [eq_inline_301]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_153
  subst c
  exact valid_inline_300

theorem eq_inline_302 : inline_302 = combine (3, 1) [placed 1 (3, 1) card_5, inline_301] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_302 : Valid inline_302 := by
  rw [eq_inline_302]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 1) valid_5
  subst c
  exact valid_inline_301

theorem eq_inline_303 : inline_303 = combine (5, 3) [placed 0 (3, 1) card_227, placed 7 (6, 5) card_245, placed 2 (2, 7) card_274] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_303 : Valid inline_303 := by
  rw [eq_inline_303]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_227
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_245
  subst c
  exact placed_valid 2 (2, 7) valid_274

theorem eq_card_560 : card_560 = combine (5, 4) [placed 5 (1, 5) card_67, placed 0 (2, 1) card_228, placed 2 (2, 5) card_373, placed 2 (2, 7) card_435, placed 0 (3, 1) card_531, inline_302, inline_303, placed 2 (0, 5) card_559] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_560 : Valid card_560 := by
  rw [eq_card_560]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_67
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_228
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 5) valid_373
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_531
  rcases hc with rfl | hc
  · exact valid_inline_302
  rcases hc with rfl | hc
  · exact valid_inline_303
  subst c
  exact placed_valid 2 (0, 5) valid_559

theorem eq_inline_304 : inline_304 = combine (2, 4) [placed 7 (2, 7) card_1, placed 0 (0, 2) card_57] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_304 : Valid inline_304 := by
  rw [eq_inline_304]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 7) valid_1
  subst c
  exact placed_valid 0 (0, 2) valid_57

theorem eq_card_561 : card_561 = combine (2, 7) [placed 0 (1, 3) card_154, placed 2 (0, 10) card_319, placed 0 (0, 3) card_335, inline_304] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_561 : Valid card_561 := by
  rw [eq_card_561]
  apply combination_rule (2, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_154
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 10) valid_319
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_335
  subst c
  exact valid_inline_304

theorem eq_inline_305 : inline_305 = combine (3, 5) [placed 4 (4, 1) card_13, placed 0 (2, 1) card_14, placed 4 (4, 1) card_33, placed 0 (1, 2) card_122, placed 2 (1, 6) card_388] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_305 : Valid inline_305 := by
  rw [eq_inline_305]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_122
  subst c
  exact placed_valid 2 (1, 6) valid_388

theorem eq_card_562 : card_562 = combine (3, 3) [placed 5 (0, 4) card_52, placed 6 (4, 7) card_506, inline_305] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_562 : Valid card_562 := by
  rw [eq_card_562]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_506
  subst c
  exact valid_inline_305

theorem eq_inline_306 : inline_306 = combine (2, 6) [placed 7 (2, 7) card_0, placed 2 (1, 7) card_393] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_306 : Valid inline_306 := by
  rw [eq_inline_306]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 7) valid_0
  subst c
  exact placed_valid 2 (1, 7) valid_393

theorem eq_inline_307 : inline_307 = combine (2, 4) [placed 6 (5, 5) card_0, inline_306] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_307 : Valid inline_307 := by
  rw [eq_inline_307]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 5) valid_0
  subst c
  exact valid_inline_306

theorem eq_inline_308 : inline_308 = combine (3, 3) [placed 6 (3, 7) card_11, placed 7 (4, 6) card_38] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_308 : Valid inline_308 := by
  rw [eq_inline_308]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 7) valid_11
  subst c
  exact placed_valid 7 (4, 6) valid_38

theorem eq_inline_309 : inline_309 = combine (3, 6) [placed 2 (3, 7) card_15, inline_308] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_309 : Valid inline_309 := by
  rw [eq_inline_309]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_15
  subst c
  exact valid_inline_308

theorem eq_inline_310 : inline_310 = combine (3, 4) [placed 2 (0, 5) card_0, inline_309] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_310 : Valid inline_310 := by
  rw [eq_inline_310]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_0
  subst c
  exact valid_inline_309

theorem eq_inline_311 : inline_311 = combine (4, 4) [placed 2 (1, 5) card_5, inline_310] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_311 : Valid inline_311 := by
  rw [eq_inline_311]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_5
  subst c
  exact valid_inline_310

theorem eq_inline_312 : inline_312 = combine (4, 5) [placed 1 (1, 4) card_18, inline_307, inline_311] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_312 : Valid inline_312 := by
  rw [eq_inline_312]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_18
  rcases hc with rfl | hc
  · exact valid_inline_307
  subst c
  exact valid_inline_311

theorem eq_card_563 : card_563 = combine (3, 5) [placed 2 (0, 7) card_134, placed 2 (0, 7) card_180, placed 2 (1, 8) card_258, placed 2 (0, 8) card_435, placed 0 (0, 2) card_507, inline_312, placed 0 (0, 0) card_561, placed 0 (0, 1) card_562] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_563 : Valid card_563 := by
  rw [eq_card_563]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_258
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_507
  rcases hc with rfl | hc
  · exact valid_inline_312
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_561
  subst c
  exact placed_valid 0 (0, 1) valid_562

theorem eq_inline_313 : inline_313 = combine (2, 4) [placed 0 (2, 4) card_5, placed 4 (5, 3) card_453] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_313 : Valid inline_313 := by
  rw [eq_inline_313]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_5
  subst c
  exact placed_valid 4 (5, 3) valid_453

theorem eq_inline_314 : inline_314 = combine (3, 5) [placed 0 (2, 5) card_5, placed 4 (5, 2) card_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_314 : Valid inline_314 := by
  rw [eq_inline_314]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_5
  subst c
  exact placed_valid 4 (5, 2) valid_55

theorem eq_inline_315 : inline_315 = combine (2, 4) [placed 4 (5, 4) card_5, placed 4 (5, 2) card_342] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_315 : Valid inline_315 := by
  rw [eq_inline_315]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 4) valid_5
  subst c
  exact placed_valid 4 (5, 2) valid_342

theorem eq_inline_316 : inline_316 = combine (2, 5) [placed 3 (6, 4) card_102, inline_314, inline_315] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_316 : Valid inline_316 := by
  rw [eq_inline_316]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_102
  rcases hc with rfl | hc
  · exact valid_inline_314
  subst c
  exact valid_inline_315

theorem eq_inline_317 : inline_317 = combine (4, 5) [placed 7 (5, 8) card_0, inline_316] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_317 : Valid inline_317 := by
  rw [eq_inline_317]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 8) valid_0
  subst c
  exact valid_inline_316

theorem eq_inline_318 : inline_318 = combine (5, 7) [placed 4 (5, 4) card_16, placed 6 (6, 8) card_235, inline_317] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_318 : Valid inline_318 := by
  rw [eq_inline_318]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 4) valid_16
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_235
  subst c
  exact valid_inline_317

theorem eq_inline_319 : inline_319 = combine (5, 6) [placed 4 (6, 2) card_67, placed 3 (7, 3) card_134, placed 3 (7, 3) card_180, placed 7 (9, 7) card_327, placed 0 (2, 2) card_504, placed 3 (7, 4) card_558, inline_318] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_319 : Valid inline_319 := by
  rw [eq_inline_319]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_67
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 3) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 3) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 7 (9, 7) valid_327
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_504
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_558
  subst c
  exact valid_inline_318

theorem eq_inline_320 : inline_320 = combine (5, 5) [placed 1 (2, 4) card_44, inline_313, inline_319, placed 1 (1, 1) card_560, placed 1 (0, 3) card_563] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_320 : Valid inline_320 := by
  rw [eq_inline_320]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_44
  rcases hc with rfl | hc
  · exact valid_inline_313
  rcases hc with rfl | hc
  · exact valid_inline_319
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_560
  subst c
  exact placed_valid 1 (0, 3) valid_563

theorem eq_inline_321 : inline_321 = combine (5, 4) [placed 1 (1, 3) card_12, placed 5 (1, 5) card_12, placed 1 (2, 1) card_79, placed 1 (1, 2) card_135, placed 5 (1, 6) card_182, inline_320] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_321 : Valid inline_321 := by
  rw [eq_inline_321]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 1) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_135
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_182
  subst c
  exact valid_inline_320

theorem eq_card_564 : card_564 = combine (4, 4) [placed 1 (1, 1) card_119, placed 4 (4, 0) card_497, placed 0 (0, 0) card_498, inline_321] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_564 : Valid card_564 := by
  rw [eq_card_564]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_119
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_497
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_498
  subst c
  exact valid_inline_321

theorem eq_inline_322 : inline_322 = combine (5, 3) [placed 2 (2, 3) card_5, placed 0 (1, 1) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_322 : Valid inline_322 := by
  rw [eq_inline_322]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 3) valid_5
  subst c
  exact placed_valid 0 (1, 1) valid_179

theorem eq_inline_323 : inline_323 = combine (1, 3) [placed 2 (1, 3) card_4, placed 0 (0, 0) card_142] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_323 : Valid inline_323 := by
  rw [eq_inline_323]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 3) valid_4
  subst c
  exact placed_valid 0 (0, 0) valid_142

theorem eq_card_565 : card_565 = combine (5, 2) [placed 5 (1, 3) card_140, inline_322, inline_323] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_565 : Valid card_565 := by
  rw [eq_card_565]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 3) valid_140
  rcases hc with rfl | hc
  · exact valid_inline_322
  subst c
  exact valid_inline_323

theorem eq_card_566 : card_566 = combine (3, 5) [placed 1 (0, 2) card_116, placed 5 (0, 6) card_116, placed 1 (0, 2) card_172, placed 5 (0, 6) card_172, placed 0 (1, 1) card_182, placed 3 (6, 1) card_565] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_566 : Valid card_566 := by
  rw [eq_card_566]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_172
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_172
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_182
  subst c
  exact placed_valid 3 (6, 1) valid_565

theorem eq_inline_324 : inline_324 = combine (4, 3) [placed 1 (4, 2) card_5, placed 7 (6, 5) card_92] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_324 : Valid inline_324 := by
  rw [eq_inline_324]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 2) valid_5
  subst c
  exact placed_valid 7 (6, 5) valid_92

theorem eq_inline_325 : inline_325 = combine (4, 2) [placed 2 (3, 5) card_94, placed 2 (3, 6) card_102, inline_324] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_325 : Valid inline_325 := by
  rw [eq_inline_325]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_94
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_102
  subst c
  exact valid_inline_324

theorem eq_inline_326 : inline_326 = combine (4, 4) [placed 6 (7, 5) card_0, inline_325] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_326 : Valid inline_326 := by
  rw [eq_inline_326]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 5) valid_0
  subst c
  exact valid_inline_325

theorem eq_inline_327 : inline_327 = combine (6, 5) [placed 5 (3, 5) card_16, placed 7 (7, 6) card_235, inline_326] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_327 : Valid inline_327 := by
  rw [eq_inline_327]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_16
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_235
  subst c
  exact valid_inline_326

theorem eq_inline_328 : inline_328 = combine (5, 5) [placed 5 (1, 6) card_67, placed 2 (2, 7) card_134, placed 2 (2, 7) card_180, placed 6 (6, 9) card_327, placed 1 (1, 2) card_504, placed 2 (3, 7) card_558, inline_327] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_328 : Valid inline_328 := by
  rw [eq_inline_328]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_67
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 9) valid_327
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_504
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_558
  subst c
  exact valid_inline_327

theorem eq_card_567 : card_567 = combine (4, 5) [placed 2 (3, 6) card_27, placed 0 (3, 2) card_44, placed 0 (0, 1) card_560, placed 0 (2, 0) card_563, inline_328] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_567 : Valid card_567 := by
  rw [eq_card_567]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_560
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_563
  subst c
  exact valid_inline_328

theorem eq_inline_329 : inline_329 = combine (4, 3) [placed 3 (7, 1) card_255, placed 4 (4, 0) card_496] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_329 : Valid inline_329 := by
  rw [eq_inline_329]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 1) valid_255
  subst c
  exact placed_valid 4 (4, 0) valid_496

theorem eq_inline_330 : inline_330 = combine (6, 4) [placed 2 (3, 5) card_24, placed 5 (2, 5) card_77] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_330 : Valid inline_330 := by
  rw [eq_inline_330]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_24
  subst c
  exact placed_valid 5 (2, 5) valid_77

theorem eq_inline_331 : inline_331 = combine (3, 7) [placed 0 (3, 3) card_6, placed 3 (5, 3) card_132] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_331 : Valid inline_331 := by
  rw [eq_inline_331]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_6
  subst c
  exact placed_valid 3 (5, 3) valid_132

theorem eq_inline_332 : inline_332 = combine (3, 7) [placed 4 (3, 3) card_6, placed 4 (4, 3) card_124] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_332 : Valid inline_332 := by
  rw [eq_inline_332]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 3) valid_6
  subst c
  exact placed_valid 4 (4, 3) valid_124

theorem eq_inline_333 : inline_333 = combine (3, 6) [placed 3 (4, 3) card_8, placed 4 (5, 3) card_387, inline_331, inline_332] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_333 : Valid inline_333 := by
  rw [eq_inline_333]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_387
  rcases hc with rfl | hc
  · exact valid_inline_331
  subst c
  exact valid_inline_332

theorem eq_inline_334 : inline_334 = combine (3, 3) [placed 5 (3, 5) card_3, inline_333] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_334 : Valid inline_334 := by
  rw [eq_inline_334]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_3
  subst c
  exact valid_inline_333

theorem eq_inline_335 : inline_335 = combine (3, 5) [placed 3 (6, 4) card_52, inline_330, inline_334] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_335 : Valid inline_335 := by
  rw [eq_inline_335]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_52
  rcases hc with rfl | hc
  · exact valid_inline_330
  subst c
  exact valid_inline_334

theorem eq_inline_336 : inline_336 = combine (5, 4) [placed 1 (2, 1) card_79, placed 5 (1, 5) card_189, placed 5 (0, 7) card_518, inline_335, placed 2 (1, 7) card_565, placed 1 (0, 1) card_567] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_336 : Valid inline_336 := by
  rw [eq_inline_336]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 1) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_518
  rcases hc with rfl | hc
  · exact valid_inline_335
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_565
  subst c
  exact placed_valid 1 (0, 1) valid_567

theorem eq_card_568 : card_568 = combine (4, 4) [placed 1 (1, 1) card_110, placed 4 (4, 0) card_497, inline_329, inline_336] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_568 : Valid card_568 := by
  rw [eq_card_568]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_110
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_497
  rcases hc with rfl | hc
  · exact valid_inline_329
  subst c
  exact valid_inline_336

theorem eq_inline_337 : inline_337 = combine (6, 6) [placed 0 (3, 5) card_5, placed 0 (5, 2) card_54] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_337 : Valid inline_337 := by
  rw [eq_inline_337]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 5) valid_5
  subst c
  exact placed_valid 0 (5, 2) valid_54

theorem eq_inline_338 : inline_338 = combine (5, 3) [placed 1 (0, 2) card_68, inline_337] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_338 : Valid inline_338 := by
  rw [eq_inline_338]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_68
  subst c
  exact valid_inline_337

theorem eq_inline_339 : inline_339 = combine (6, 3) [placed 7 (6, 3) card_169, placed 2 (3, 6) card_202] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_339 : Valid inline_339 := by
  rw [eq_inline_339]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 3) valid_169
  subst c
  exact placed_valid 2 (3, 6) valid_202

theorem eq_inline_340 : inline_340 = combine (6, 5) [placed 0 (3, 4) card_8, inline_338, inline_339] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_340 : Valid inline_340 := by
  rw [eq_inline_340]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_8
  rcases hc with rfl | hc
  · exact valid_inline_338
  subst c
  exact valid_inline_339

theorem eq_inline_341 : inline_341 = combine (5, 3) [placed 1 (0, 2) card_68, placed 0 (3, 0) card_495] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_341 : Valid inline_341 := by
  rw [eq_inline_341]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_68
  subst c
  exact placed_valid 0 (3, 0) valid_495

theorem eq_inline_342 : inline_342 = combine (6, 3) [placed 0 (3, 2) card_99, placed 7 (6, 3) card_169] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_342 : Valid inline_342 := by
  rw [eq_inline_342]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_99
  subst c
  exact placed_valid 7 (6, 3) valid_169

theorem eq_inline_343 : inline_343 = combine (4, 6) [placed 1 (2, 5) card_11, placed 1 (0, 2) card_288] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_343 : Valid inline_343 := by
  rw [eq_inline_343]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_11
  subst c
  exact placed_valid 1 (0, 2) valid_288

theorem eq_inline_344 : inline_344 = combine (6, 5) [placed 5 (2, 6) card_9, inline_342, inline_343] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_344 : Valid inline_344 := by
  rw [eq_inline_344]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 6) valid_9
  rcases hc with rfl | hc
  · exact valid_inline_342
  subst c
  exact valid_inline_343

theorem eq_card_569 : card_569 = combine (5, 5) [placed 1 (0, 2) card_287, placed 2 (2, 9) card_322, placed 1 (2, 4) card_457, inline_340, inline_341, inline_344] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_569 : Valid card_569 := by
  rw [eq_card_569]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_287
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_322
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_457
  rcases hc with rfl | hc
  · exact valid_inline_340
  rcases hc with rfl | hc
  · exact valid_inline_341
  subst c
  exact valid_inline_344

theorem eq_inline_345 : inline_345 = combine (4, 5) [placed 3 (4, 3) card_5, placed 2 (3, 9) card_446] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_345 : Valid inline_345 := by
  rw [eq_inline_345]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_5
  subst c
  exact placed_valid 2 (3, 9) valid_446

theorem eq_inline_346 : inline_346 = combine (5, 3) [placed 5 (2, 4) card_20, placed 1 (2, 3) card_29, placed 0 (2, 0) card_331] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_346 : Valid inline_346 := by
  rw [eq_inline_346]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_20
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_29
  subst c
  exact placed_valid 0 (2, 0) valid_331

theorem eq_inline_347 : inline_347 = combine (2, 3) [placed 0 (0, 3) card_1, inline_346] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_347 : Valid inline_347 := by
  rw [eq_inline_347]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_1
  subst c
  exact valid_inline_346

theorem eq_card_570 : card_570 = combine (4, 3) [placed 2 (3, 7) card_150, placed 0 (0, 1) card_283, inline_345, inline_347] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_570 : Valid card_570 := by
  rw [eq_card_570]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_150
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_283
  rcases hc with rfl | hc
  · exact valid_inline_345
  subst c
  exact valid_inline_347

theorem eq_inline_348 : inline_348 = combine (5, 6) [placed 1 (0, 3) card_287, placed 1 (0, 3) card_288, placed 0 (2, 4) card_345, placed 1 (2, 5) card_457] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_348 : Valid inline_348 := by
  rw [eq_inline_348]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_287
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_288
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_345
  subst c
  exact placed_valid 1 (2, 5) valid_457

theorem eq_inline_349 : inline_349 = combine (4, 7) [placed 7 (4, 7) card_2, inline_348] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_349 : Valid inline_349 := by
  rw [eq_inline_349]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 7) valid_2
  subst c
  exact valid_inline_348

theorem eq_inline_350 : inline_350 = combine (4, 3) [placed 3 (4, 3) card_5, placed 2 (3, 9) card_446] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_350 : Valid inline_350 := by
  rw [eq_inline_350]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_5
  subst c
  exact placed_valid 2 (3, 9) valid_446

theorem eq_inline_351 : inline_351 = combine (4, 5) [placed 7 (4, 7) card_0, inline_350] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_351 : Valid inline_351 := by
  rw [eq_inline_351]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 7) valid_0
  subst c
  exact valid_inline_350

theorem eq_inline_352 : inline_352 = combine (4, 3) [placed 3 (4, 3) card_5, placed 0 (0, 1) card_283] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_352 : Valid inline_352 := by
  rw [eq_inline_352]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_283

theorem eq_inline_353 : inline_353 = combine (4, 5) [placed 7 (4, 7) card_0, inline_352] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_353 : Valid inline_353 := by
  rw [eq_inline_353]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 7) valid_0
  subst c
  exact valid_inline_352

theorem eq_inline_354 : inline_354 = combine (5, 3) [placed 5 (4, 6) card_5, placed 1 (2, 3) card_29] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_354 : Valid inline_354 := by
  rw [eq_inline_354]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 6) valid_5
  subst c
  exact placed_valid 1 (2, 3) valid_29

theorem eq_inline_355 : inline_355 = combine (4, 3) [placed 2 (4, 7) card_7, inline_354, placed 2 (3, 9) card_446] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_355 : Valid inline_355 := by
  rw [eq_inline_355]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 7) valid_7
  rcases hc with rfl | hc
  · exact valid_inline_354
  subst c
  exact placed_valid 2 (3, 9) valid_446

theorem eq_inline_356 : inline_356 = combine (4, 5) [placed 7 (4, 7) card_0, inline_355] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_356 : Valid inline_356 := by
  rw [eq_inline_356]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 7) valid_0
  subst c
  exact valid_inline_355

theorem eq_inline_357 : inline_357 = combine (2, 3) [placed 0 (0, 3) card_1, inline_356] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_357 : Valid inline_357 := by
  rw [eq_inline_357]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_1
  subst c
  exact valid_inline_356

theorem eq_card_571 : card_571 = combine (4, 4) [placed 2 (3, 7) card_250, placed 0 (0, 1) card_569, inline_349, inline_351, inline_353, placed 0 (0, 0) card_570, inline_357] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_571 : Valid card_571 := by
  rw [eq_card_571]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_250
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_569
  rcases hc with rfl | hc
  · exact valid_inline_349
  rcases hc with rfl | hc
  · exact valid_inline_351
  rcases hc with rfl | hc
  · exact valid_inline_353
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_570
  subst c
  exact valid_inline_357

theorem eq_inline_358 : inline_358 = combine (2, 6) [placed 4 (4, 6) card_5, placed 2 (1, 7) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_358 : Valid inline_358 := by
  rw [eq_inline_358]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 6) valid_5
  subst c
  exact placed_valid 2 (1, 7) valid_78

theorem eq_card_572 : card_572 = combine (4, 6) [placed 5 (0, 7) card_97, placed 1 (0, 6) card_98, inline_358, placed 0 (0, 0) card_571] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_572 : Valid card_572 := by
  rw [eq_card_572]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_97
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 6) valid_98
  rcases hc with rfl | hc
  · exact valid_inline_358
  subst c
  exact placed_valid 0 (0, 0) valid_571

theorem eq_inline_359 : inline_359 = combine (3, 5) [placed 1 (2, 3) card_8, placed 1 (0, 3) card_115, placed 3 (4, 3) card_197, placed 0 (0, 2) card_286, placed 0 (0, 2) card_339] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_359 : Valid inline_359 := by
  rw [eq_inline_359]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_286
  subst c
  exact placed_valid 0 (0, 2) valid_339

theorem eq_inline_360 : inline_360 = combine (3, 5) [placed 0 (3, 2) card_7, placed 1 (2, 3) card_8, placed 4 (4, 2) card_9, placed 5 (1, 7) card_473] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_360 : Valid inline_360 := by
  rw [eq_inline_360]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_9
  subst c
  exact placed_valid 5 (1, 7) valid_473

theorem eq_inline_361 : inline_361 = combine (3, 5) [placed 1 (2, 3) card_8, placed 0 (0, 2) card_403, placed 0 (0, 3) card_487, placed 0 (0, 2) card_492] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_361 : Valid inline_361 := by
  rw [eq_inline_361]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_403
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_487
  subst c
  exact placed_valid 0 (0, 2) valid_492

theorem eq_inline_362 : inline_362 = combine (3, 5) [placed 0 (0, 2) card_87, placed 0 (0, 3) card_487] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_362 : Valid inline_362 := by
  rw [eq_inline_362]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_87
  subst c
  exact placed_valid 0 (0, 3) valid_487

theorem eq_inline_363 : inline_363 = combine (1, 7) [placed 0 (0, 3) card_107, placed 0 (0, 0) card_572] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_363 : Valid inline_363 := by
  rw [eq_inline_363]
  apply combination_rule (1, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_107
  subst c
  exact placed_valid 0 (0, 0) valid_572

theorem eq_inline_364 : inline_364 = combine (3, 5) [placed 4 (4, 2) card_9, placed 0 (0, 2) card_249, placed 7 (5, 6) card_383, placed 0 (0, 2) card_403] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_364 : Valid inline_364 := by
  rw [eq_inline_364]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_249
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_383
  subst c
  exact placed_valid 0 (0, 2) valid_403

theorem eq_card_573 : card_573 = combine (3, 6) [placed 0 (0, 2) card_384, placed 0 (0, 2) card_385, placed 0 (0, 2) card_493, placed 0 (0, 2) card_494, inline_359, inline_360, inline_361, inline_362, inline_363, inline_364] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_573 : Valid card_573 := by
  rw [eq_card_573]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_384
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_385
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_493
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_494
  rcases hc with rfl | hc
  · exact valid_inline_359
  rcases hc with rfl | hc
  · exact valid_inline_360
  rcases hc with rfl | hc
  · exact valid_inline_361
  rcases hc with rfl | hc
  · exact valid_inline_362
  rcases hc with rfl | hc
  · exact valid_inline_363
  subst c
  exact valid_inline_364

theorem eq_inline_365 : inline_365 = combine (3, 3) [placed 1 (1, 2) card_43, placed 6 (4, 6) card_64] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_365 : Valid inline_365 := by
  rw [eq_inline_365]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_43
  subst c
  exact placed_valid 6 (4, 6) valid_64

theorem eq_inline_366 : inline_366 = combine (4, 4) [placed 7 (4, 5) card_5, placed 0 (1, 1) card_223] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_366 : Valid inline_366 := by
  rw [eq_inline_366]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_5
  subst c
  exact placed_valid 0 (1, 1) valid_223

theorem eq_inline_367 : inline_367 = combine (4, 2) [placed 0 (1, 2) card_5, inline_366] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_367 : Valid inline_367 := by
  rw [eq_inline_367]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_5
  subst c
  exact valid_inline_366

theorem eq_inline_368 : inline_368 = combine (4, 2) [placed 7 (4, 5) card_5, placed 6 (5, 6) card_236] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_368 : Valid inline_368 := by
  rw [eq_inline_368]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_5
  subst c
  exact placed_valid 6 (5, 6) valid_236

theorem eq_inline_369 : inline_369 = combine (4, 4) [placed 0 (3, 2) card_18, placed 6 (4, 6) card_61, inline_368] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_369 : Valid inline_369 := by
  rw [eq_inline_369]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_18
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_61
  subst c
  exact valid_inline_368

theorem eq_inline_370 : inline_370 = combine (3, 2) [placed 1 (1, 2) card_130, inline_365, inline_367, inline_369] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_370 : Valid inline_370 := by
  rw [eq_inline_370]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_130
  rcases hc with rfl | hc
  · exact valid_inline_365
  rcases hc with rfl | hc
  · exact valid_inline_367
  subst c
  exact valid_inline_369

theorem eq_card_574 : card_574 = combine (4, 5) [placed 4 (5, 2) card_184, placed 1 (0, 2) card_384, placed 1 (0, 2) card_385, placed 1 (0, 2) card_493, placed 1 (0, 2) card_494, inline_370] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_574 : Valid card_574 := by
  rw [eq_card_574]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_184
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_384
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_385
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_493
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_494
  subst c
  exact valid_inline_370

theorem eq_inline_371 : inline_371 = combine (2, 4) [placed 6 (4, 4) card_3, placed 0 (2, 3) card_8] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_371 : Valid inline_371 := by
  rw [eq_inline_371]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_3
  subst c
  exact placed_valid 0 (2, 3) valid_8

theorem eq_inline_372 : inline_372 = combine (2, 4) [placed 6 (4, 4) card_3, placed 5 (2, 4) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_372 : Valid inline_372 := by
  rw [eq_inline_372]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_3
  subst c
  exact placed_valid 5 (2, 4) valid_6

theorem eq_inline_373 : inline_373 = combine (6, 4) [inline_372, placed 3 (7, 4) card_554] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_373 : Valid inline_373 := by
  rw [eq_inline_373]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_372
  subst c
  exact placed_valid 3 (7, 4) valid_554

theorem eq_inline_374 : inline_374 = combine (6, 4) [placed 1 (0, 3) card_280, placed 3 (7, 4) card_554] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_374 : Valid inline_374 := by
  rw [eq_inline_374]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_280
  subst c
  exact placed_valid 3 (7, 4) valid_554

theorem eq_card_575 : card_575 = combine (5, 4) [placed 0 (2, 1) card_257, placed 0 (0, 0) card_326, inline_371, inline_373, inline_374] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_575 : Valid card_575 := by
  rw [eq_card_575]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_257
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_326
  rcases hc with rfl | hc
  · exact valid_inline_371
  rcases hc with rfl | hc
  · exact valid_inline_373
  subst c
  exact valid_inline_374

theorem block08_valid : Valid card_512 ∧ Valid card_513 ∧ Valid card_514 ∧ Valid card_515 ∧ Valid card_516 ∧ Valid card_517 ∧ Valid card_518 ∧ Valid card_519 ∧ Valid card_520 ∧ Valid card_521 ∧ Valid card_522 ∧ Valid card_523 ∧ Valid card_524 ∧ Valid card_525 ∧ Valid card_526 ∧ Valid card_527 ∧ Valid card_528 ∧ Valid card_529 ∧ Valid card_530 ∧ Valid card_531 ∧ Valid card_532 ∧ Valid card_533 ∧ Valid card_534 ∧ Valid card_535 ∧ Valid card_536 ∧ Valid card_537 ∧ Valid card_538 ∧ Valid card_539 ∧ Valid card_540 ∧ Valid card_541 ∧ Valid card_542 ∧ Valid card_543 ∧ Valid card_544 ∧ Valid card_545 ∧ Valid card_546 ∧ Valid card_547 ∧ Valid card_548 ∧ Valid card_549 ∧ Valid card_550 ∧ Valid card_551 ∧ Valid card_552 ∧ Valid card_553 ∧ Valid card_554 ∧ Valid card_555 ∧ Valid card_556 ∧ Valid card_557 ∧ Valid card_558 ∧ Valid card_559 ∧ Valid card_560 ∧ Valid card_561 ∧ Valid card_562 ∧ Valid card_563 ∧ Valid card_564 ∧ Valid card_565 ∧ Valid card_566 ∧ Valid card_567 ∧ Valid card_568 ∧ Valid card_569 ∧ Valid card_570 ∧ Valid card_571 ∧ Valid card_572 ∧ Valid card_573 ∧ Valid card_574 ∧ Valid card_575 ∧ True :=
  ⟨valid_512, valid_513, valid_514, valid_515, valid_516, valid_517, valid_518, valid_519, valid_520, valid_521, valid_522, valid_523, valid_524, valid_525, valid_526, valid_527, valid_528, valid_529, valid_530, valid_531, valid_532, valid_533, valid_534, valid_535, valid_536, valid_537, valid_538, valid_539, valid_540, valid_541, valid_542, valid_543, valid_544, valid_545, valid_546, valid_547, valid_548, valid_549, valid_550, valid_551, valid_552, valid_553, valid_554, valid_555, valid_556, valid_557, valid_558, valid_559, valid_560, valid_561, valid_562, valid_563, valid_564, valid_565, valid_566, valid_567, valid_568, valid_569, valid_570, valid_571, valid_572, valid_573, valid_574, valid_575, True.intro⟩

end OAI.Snaky21.Certificate
