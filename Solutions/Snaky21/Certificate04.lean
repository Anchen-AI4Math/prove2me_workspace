import Definitions.Def_Snaky21Data04
import Solutions.Snaky21.Geometry
import Solutions.Snaky21.Certificate03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_card_256 : card_256 = combine (3, 4) [placed 0 (0, 3) card_5, placed 0 (0, 0) card_255] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_256 : Valid card_256 := by
  rw [eq_card_256]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_255

theorem eq_card_257 : card_257 = combine (4, 3) [placed 1 (0, 3) card_7, placed 5 (0, 4) card_9, placed 0 (1, 0) card_256] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_257 : Valid card_257 := by
  rw [eq_card_257]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_9
  subst c
  exact placed_valid 0 (1, 0) valid_256

theorem eq_card_258 : card_258 = combine (3, 3) [placed 0 (0, 2) card_8, placed 2 (0, 6) card_161, placed 2 (0, 6) card_162, placed 0 (0, 0) card_256] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_258 : Valid card_258 := by
  rw [eq_card_258]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_161
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_162
  subst c
  exact placed_valid 0 (0, 0) valid_256

theorem eq_card_259 : card_259 = combine (2, 4) [placed 0 (1, 1) card_15, placed 2 (0, 5) card_159] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_259 : Valid card_259 := by
  rw [eq_card_259]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_15
  subst c
  exact placed_valid 2 (0, 5) valid_159

theorem eq_card_260 : card_260 = combine (3, 0) [placed 2 (0, 1) card_5, placed 3 (4, 0) card_208] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_260 : Valid card_260 := by
  rw [eq_card_260]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 3 (4, 0) valid_208

theorem eq_card_261 : card_261 = combine (1, 3) [placed 1 (0, 0) card_3, placed 0 (0, 0) card_129] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_261 : Valid card_261 := by
  rw [eq_card_261]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_3
  subst c
  exact placed_valid 0 (0, 0) valid_129

theorem eq_card_262 : card_262 = combine (1, 1) [placed 0 (1, 0) card_15, placed 5 (0, 3) card_66] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_262 : Valid card_262 := by
  rw [eq_card_262]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_15
  subst c
  exact placed_valid 5 (0, 3) valid_66

theorem eq_card_263 : card_263 = combine (3, 4) [placed 0 (3, 0) card_7, placed 4 (4, 0) card_9, placed 3 (4, 1) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_263 : Valid card_263 := by
  rw [eq_card_263]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_9
  subst c
  exact placed_valid 3 (4, 1) valid_78

theorem eq_card_264 : card_264 = combine (1, 4) [placed 1 (0, 1) card_8, placed 5 (0, 4) card_201] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_264 : Valid card_264 := by
  rw [eq_card_264]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_8
  subst c
  exact placed_valid 5 (0, 4) valid_201

theorem eq_card_265 : card_265 = combine (1, 4) [placed 7 (1, 4) card_4, placed 1 (0, 1) card_93] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_265 : Valid card_265 := by
  rw [eq_card_265]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_4
  subst c
  exact placed_valid 1 (0, 1) valid_93

theorem eq_card_266 : card_266 = combine (0, 6) [placed 0 (0, 2) card_6, placed 0 (0, 3) card_16, placed 2 (0, 7) card_113] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_266 : Valid card_266 := by
  rw [eq_card_266]
  apply combination_rule (0, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_16
  subst c
  exact placed_valid 2 (0, 7) valid_113

theorem eq_card_267 : card_267 = combine (2, 5) [placed 1 (1, 2) card_8, placed 0 (1, 2) card_17, placed 0 (1, 0) card_75, placed 5 (0, 6) card_179, placed 4 (2, 0) card_266] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_267 : Valid card_267 := by
  rw [eq_card_267]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_75
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_179
  subst c
  exact placed_valid 4 (2, 0) valid_266

theorem eq_card_268 : card_268 = combine (1, 4) [placed 6 (1, 6) card_7, placed 1 (0, 2) card_8, placed 6 (2, 6) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_268 : Valid card_268 := by
  rw [eq_card_268]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_8
  subst c
  exact placed_valid 6 (2, 6) valid_9

theorem eq_card_269 : card_269 = combine (1, 5) [placed 2 (1, 6) card_7, placed 4 (1, 2) card_21] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_269 : Valid card_269 := by
  rw [eq_card_269]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_7
  subst c
  exact placed_valid 4 (1, 2) valid_21

theorem eq_card_270 : card_270 = combine (4, 2) [placed 7 (4, 2) card_70, placed 1 (0, 1) card_106, placed 1 (1, 0) card_122, placed 1 (0, 1) card_269] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_270 : Valid card_270 := by
  rw [eq_card_270]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 2) valid_70
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_106
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 0) valid_122
  subst c
  exact placed_valid 1 (0, 1) valid_269

theorem eq_card_271 : card_271 = combine (2, 3) [placed 2 (0, 3) card_5, placed 4 (3, 0) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_271 : Valid card_271 := by
  rw [eq_card_271]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_52

theorem eq_card_272 : card_272 = combine (2, 1) [placed 0 (0, 1) card_5, placed 0 (2, 0) card_39] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_272 : Valid card_272 := by
  rw [eq_card_272]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact placed_valid 0 (2, 0) valid_39

theorem eq_card_273 : card_273 = combine (3, 3) [placed 0 (0, 3) card_2, placed 0 (3, 0) card_206] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_273 : Valid card_273 := by
  rw [eq_card_273]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_2
  subst c
  exact placed_valid 0 (3, 0) valid_206

theorem eq_card_274 : card_274 = combine (3, 2) [placed 0 (2, 0) card_13, placed 5 (0, 3) card_44, placed 3 (4, 2) card_83] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_274 : Valid card_274 := by
  rw [eq_card_274]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_44
  subst c
  exact placed_valid 3 (4, 2) valid_83

theorem eq_card_275 : card_275 = combine (4, 2) [placed 5 (1, 2) card_16, placed 0 (1, 1) card_24, placed 4 (5, 0) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_275 : Valid card_275 := by
  rw [eq_card_275]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 2) valid_16
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_24
  subst c
  exact placed_valid 4 (5, 0) valid_179

theorem eq_card_276 : card_276 = combine (2, 4) [placed 6 (2, 6) card_44, placed 6 (2, 6) card_52, placed 5 (0, 6) card_155, placed 1 (0, 2) card_275] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_276 : Valid card_276 := by
  rw [eq_card_276]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_155
  subst c
  exact placed_valid 1 (0, 2) valid_275

theorem eq_card_277 : card_277 = combine (1, 3) [placed 4 (5, 2) card_0, placed 4 (4, 0) card_69] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_277 : Valid card_277 := by
  rw [eq_card_277]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_0
  subst c
  exact placed_valid 4 (4, 0) valid_69

theorem eq_card_278 : card_278 = combine (4, 2) [placed 5 (0, 2) card_6, placed 0 (0, 0) card_277] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_278 : Valid card_278 := by
  rw [eq_card_278]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 2) valid_6
  subst c
  exact placed_valid 0 (0, 0) valid_277

theorem eq_card_279 : card_279 = combine (4, 3) [placed 5 (0, 3) card_6, placed 0 (1, 0) card_141] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_279 : Valid card_279 := by
  rw [eq_card_279]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_6
  subst c
  exact placed_valid 0 (1, 0) valid_141

theorem eq_card_280 : card_280 = combine (1, 2) [placed 7 (1, 4) card_3, placed 0 (1, 2) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_280 : Valid card_280 := by
  rw [eq_card_280]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_3
  subst c
  exact placed_valid 0 (1, 2) valid_6

theorem eq_card_281 : card_281 = combine (1, 3) [placed 4 (4, 3) card_2, placed 1 (0, 0) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_281 : Valid card_281 := by
  rw [eq_card_281]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_2
  subst c
  exact placed_valid 1 (0, 0) valid_3

theorem eq_card_282 : card_282 = combine (3, 2) [placed 5 (0, 3) card_20, placed 1 (0, 2) card_29, placed 0 (0, 0) card_92] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_282 : Valid card_282 := by
  rw [eq_card_282]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_20
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_29
  subst c
  exact placed_valid 0 (0, 0) valid_92

theorem eq_card_283 : card_283 = combine (2, 2) [placed 0 (0, 2) card_1, placed 0 (2, 0) card_282] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_283 : Valid card_283 := by
  rw [eq_card_283]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_1
  subst c
  exact placed_valid 0 (2, 0) valid_282

theorem eq_card_284 : card_284 = combine (1, 3) [placed 1 (0, 3) card_8, placed 0 (0, 3) card_17, placed 2 (0, 7) card_19, placed 0 (0, 1) card_75] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_284 : Valid card_284 := by
  rw [eq_card_284]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_19
  subst c
  exact placed_valid 0 (0, 1) valid_75

theorem eq_card_285 : card_285 = combine (4, 3) [placed 1 (0, 3) card_6, placed 0 (1, 2) card_26, placed 0 (1, 0) card_117] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_285 : Valid card_285 := by
  rw [eq_card_285]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_26
  subst c
  exact placed_valid 0 (1, 0) valid_117

theorem eq_card_286 : card_286 = combine (4, 2) [placed 7 (4, 4) card_35, placed 3 (6, 1) card_253] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_286 : Valid card_286 := by
  rw [eq_card_286]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 4) valid_35
  subst c
  exact placed_valid 3 (6, 1) valid_253

theorem eq_card_287 : card_287 = combine (1, 6) [placed 6 (1, 6) card_169, placed 3 (5, 2) card_230] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_287 : Valid card_287 := by
  rw [eq_card_287]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_169
  subst c
  exact placed_valid 3 (5, 2) valid_230

theorem eq_card_288 : card_288 = combine (1, 5) [placed 5 (0, 5) card_54, placed 0 (0, 0) card_68] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_288 : Valid card_288 := by
  rw [eq_card_288]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_54
  subst c
  exact placed_valid 0 (0, 0) valid_68

theorem eq_card_289 : card_289 = combine (1, 2) [placed 0 (0, 0) card_22, placed 2 (0, 5) card_28, placed 6 (2, 5) card_126] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_289 : Valid card_289 := by
  rw [eq_card_289]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_28
  subst c
  exact placed_valid 6 (2, 5) valid_126

theorem eq_card_290 : card_290 = combine (2, 1) [placed 4 (4, 1) card_5, placed 0 (0, 0) card_203] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_290 : Valid card_290 := by
  rw [eq_card_290]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_203

theorem eq_card_291 : card_291 = combine (3, 4) [placed 4 (3, 0) card_7, placed 3 (4, 1) card_25] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_291 : Valid card_291 := by
  rw [eq_card_291]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_7
  subst c
  exact placed_valid 3 (4, 1) valid_25

theorem eq_card_292 : card_292 = combine (4, 3) [placed 1 (0, 3) card_6, placed 1 (0, 2) card_19, placed 0 (0, 0) card_214] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_292 : Valid card_292 := by
  rw [eq_card_292]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_19
  subst c
  exact placed_valid 0 (0, 0) valid_214

theorem eq_card_293 : card_293 = combine (4, 3) [placed 1 (1, 2) card_17, placed 4 (4, 0) card_56] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_293 : Valid card_293 := by
  rw [eq_card_293]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_17
  subst c
  exact placed_valid 4 (4, 0) valid_56

theorem eq_card_294 : card_294 = combine (3, 3) [placed 1 (0, 2) card_10, placed 1 (0, 2) card_48, placed 5 (0, 6) card_165] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_294 : Valid card_294 := by
  rw [eq_card_294]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_48
  subst c
  exact placed_valid 5 (0, 6) valid_165

theorem eq_card_295 : card_295 = combine (3, 1) [placed 3 (5, 1) card_34, placed 3 (6, 0) card_180] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_295 : Valid card_295 := by
  rw [eq_card_295]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 1) valid_34
  subst c
  exact placed_valid 3 (6, 0) valid_180

theorem eq_card_296 : card_296 = combine (2, 3) [placed 7 (2, 5) card_0, placed 5 (0, 5) card_132] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_296 : Valid card_296 := by
  rw [eq_card_296]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 5) valid_0
  subst c
  exact placed_valid 5 (0, 5) valid_132

theorem eq_card_297 : card_297 = combine (5, 3) [placed 7 (6, 4) card_9, placed 0 (1, 0) card_142, placed 2 (2, 6) card_162] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_297 : Valid card_297 := by
  rw [eq_card_297]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_142
  subst c
  exact placed_valid 2 (2, 6) valid_162

theorem eq_card_298 : card_298 = combine (5, 3) [placed 7 (6, 3) card_7, placed 0 (1, 0) card_142, placed 2 (2, 6) card_161] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_298 : Valid card_298 := by
  rw [eq_card_298]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_142
  subst c
  exact placed_valid 2 (2, 6) valid_161

theorem eq_card_299 : card_299 = combine (3, 5) [placed 2 (2, 7) card_12, placed 0 (0, 2) card_165, placed 4 (4, 2) card_264] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_299 : Valid card_299 := by
  rw [eq_card_299]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_165
  subst c
  exact placed_valid 4 (4, 2) valid_264

theorem eq_card_300 : card_300 = combine (2, 5) [placed 6 (2, 6) card_44, placed 6 (2, 6) card_52, placed 0 (1, 1) card_128, placed 5 (0, 6) card_155] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_300 : Valid card_300 := by
  rw [eq_card_300]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_128
  subst c
  exact placed_valid 5 (0, 6) valid_155

theorem eq_card_301 : card_301 = combine (3, 3) [placed 5 (0, 3) card_23, placed 0 (0, 0) card_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_301 : Valid card_301 := by
  rw [eq_card_301]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_23
  subst c
  exact placed_valid 0 (0, 0) valid_55

theorem eq_card_302 : card_302 = combine (5, 3) [placed 7 (5, 3) card_6, placed 2 (1, 6) card_214] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_302 : Valid card_302 := by
  rw [eq_card_302]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 3) valid_6
  subst c
  exact placed_valid 2 (1, 6) valid_214

theorem eq_card_303 : card_303 = combine (3, 4) [placed 2 (1, 6) card_55, placed 5 (0, 4) card_234] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_303 : Valid card_303 := by
  rw [eq_card_303]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_55
  subst c
  exact placed_valid 5 (0, 4) valid_234

theorem eq_card_304 : card_304 = combine (1, 4) [placed 4 (1, 1) card_7, placed 1 (0, 2) card_8, placed 6 (2, 6) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_304 : Valid card_304 := by
  rw [eq_card_304]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 1) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_8
  subst c
  exact placed_valid 6 (2, 6) valid_9

theorem eq_card_305 : card_305 = combine (1, 3) [placed 7 (1, 4) card_5, placed 2 (0, 5) card_124] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_305 : Valid card_305 := by
  rw [eq_card_305]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 2 (0, 5) valid_124

theorem eq_card_306 : card_306 = combine (4, 1) [placed 4 (4, 1) card_18, placed 7 (4, 4) card_207] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_306 : Valid card_306 := by
  rw [eq_card_306]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_18
  subst c
  exact placed_valid 7 (4, 4) valid_207

theorem eq_card_307 : card_307 = combine (4, 2) [placed 6 (4, 2) card_5, placed 0 (1, 0) card_131] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_307 : Valid card_307 := by
  rw [eq_card_307]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_131

theorem eq_card_308 : card_308 = combine (1, 5) [placed 6 (1, 6) card_44, placed 6 (1, 6) card_52, placed 0 (0, 2) card_63, placed 6 (1, 6) card_158] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_308 : Valid card_308 := by
  rw [eq_card_308]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_63
  subst c
  exact placed_valid 6 (1, 6) valid_158

theorem eq_card_309 : card_309 = combine (4, 3) [placed 1 (0, 2) card_19, placed 5 (0, 4) card_19, placed 4 (4, 0) card_115] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_309 : Valid card_309 := by
  rw [eq_card_309]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_19
  subst c
  exact placed_valid 4 (4, 0) valid_115

theorem eq_card_310 : card_310 = combine (1, 3) [placed 7 (1, 4) card_5, placed 0 (0, 1) card_76] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_310 : Valid card_310 := by
  rw [eq_card_310]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_76

theorem eq_inline_0 : inline_0 = combine (4, 1) [placed 2 (1, 1) card_5, placed 1 (0, 1) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_0 : Valid inline_0 := by
  rw [eq_inline_0]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 1) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_6

theorem eq_card_311 : card_311 = combine (3, 1) [placed 2 (0, 1) card_4, inline_0] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_311 : Valid card_311 := by
  rw [eq_card_311]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_4
  subst c
  exact valid_inline_0

theorem eq_card_312 : card_312 = combine (2, 1) [placed 5 (1, 4) card_5, placed 2 (0, 2) card_311] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_312 : Valid card_312 := by
  rw [eq_card_312]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 2 (0, 2) valid_311

theorem eq_card_313 : card_313 = combine (3, 0) [placed 2 (0, 1) card_5, placed 3 (4, 0) card_312] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_313 : Valid card_313 := by
  rw [eq_card_313]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 3 (4, 0) valid_312

theorem eq_inline_1 : inline_1 = combine (3, 0) [placed 2 (0, 1) card_5, placed 1 (1, 0) card_20] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_1 : Valid inline_1 := by
  rw [eq_inline_1]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 1 (1, 0) valid_20

theorem eq_card_314 : card_314 = combine (4, 1) [placed 5 (0, 1) card_6, placed 0 (1, 0) card_8, placed 1 (1, 0) card_17, inline_1] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_314 : Valid card_314 := by
  rw [eq_card_314]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 1) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 0) valid_17
  subst c
  exact valid_inline_1

theorem eq_card_315 : card_315 = combine (1, 4) [placed 7 (1, 4) card_5, placed 1 (0, 1) card_314] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_315 : Valid card_315 := by
  rw [eq_card_315]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_314

theorem eq_card_316 : card_316 = combine (1, 2) [placed 5 (0, 5) card_8, placed 1 (0, 2) card_314] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_316 : Valid card_316 := by
  rw [eq_card_316]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_8
  subst c
  exact placed_valid 1 (0, 2) valid_314

theorem eq_card_317 : card_317 = combine (3, 5) [placed 1 (0, 4) card_44, placed 4 (4, 2) card_60, placed 0 (2, 0) card_316] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_317 : Valid card_317 := by
  rw [eq_card_317]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_60
  subst c
  exact placed_valid 0 (2, 0) valid_316

theorem eq_card_318 : card_318 = combine (1, 3) [placed 2 (0, 6) card_10, placed 4 (1, 2) card_52, placed 6 (1, 6) card_52, placed 0 (0, 2) card_315] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_318 : Valid card_318 := by
  rw [eq_card_318]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_52
  subst c
  exact placed_valid 0 (0, 2) valid_315

theorem eq_card_319 : card_319 = combine (3, 4) [placed 5 (0, 5) card_52, placed 0 (2, 0) card_318] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_319 : Valid card_319 := by
  rw [eq_card_319]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_52
  subst c
  exact placed_valid 0 (2, 0) valid_318

theorem block04_valid : Valid card_256 ∧ Valid card_257 ∧ Valid card_258 ∧ Valid card_259 ∧ Valid card_260 ∧ Valid card_261 ∧ Valid card_262 ∧ Valid card_263 ∧ Valid card_264 ∧ Valid card_265 ∧ Valid card_266 ∧ Valid card_267 ∧ Valid card_268 ∧ Valid card_269 ∧ Valid card_270 ∧ Valid card_271 ∧ Valid card_272 ∧ Valid card_273 ∧ Valid card_274 ∧ Valid card_275 ∧ Valid card_276 ∧ Valid card_277 ∧ Valid card_278 ∧ Valid card_279 ∧ Valid card_280 ∧ Valid card_281 ∧ Valid card_282 ∧ Valid card_283 ∧ Valid card_284 ∧ Valid card_285 ∧ Valid card_286 ∧ Valid card_287 ∧ Valid card_288 ∧ Valid card_289 ∧ Valid card_290 ∧ Valid card_291 ∧ Valid card_292 ∧ Valid card_293 ∧ Valid card_294 ∧ Valid card_295 ∧ Valid card_296 ∧ Valid card_297 ∧ Valid card_298 ∧ Valid card_299 ∧ Valid card_300 ∧ Valid card_301 ∧ Valid card_302 ∧ Valid card_303 ∧ Valid card_304 ∧ Valid card_305 ∧ Valid card_306 ∧ Valid card_307 ∧ Valid card_308 ∧ Valid card_309 ∧ Valid card_310 ∧ Valid card_311 ∧ Valid card_312 ∧ Valid card_313 ∧ Valid card_314 ∧ Valid card_315 ∧ Valid card_316 ∧ Valid card_317 ∧ Valid card_318 ∧ Valid card_319 ∧ True :=
  ⟨valid_256, valid_257, valid_258, valid_259, valid_260, valid_261, valid_262, valid_263, valid_264, valid_265, valid_266, valid_267, valid_268, valid_269, valid_270, valid_271, valid_272, valid_273, valid_274, valid_275, valid_276, valid_277, valid_278, valid_279, valid_280, valid_281, valid_282, valid_283, valid_284, valid_285, valid_286, valid_287, valid_288, valid_289, valid_290, valid_291, valid_292, valid_293, valid_294, valid_295, valid_296, valid_297, valid_298, valid_299, valid_300, valid_301, valid_302, valid_303, valid_304, valid_305, valid_306, valid_307, valid_308, valid_309, valid_310, valid_311, valid_312, valid_313, valid_314, valid_315, valid_316, valid_317, valid_318, valid_319, True.intro⟩

end OAI.Snaky21.Certificate
