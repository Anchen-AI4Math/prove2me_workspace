import Definitions.Def_Snaky21Data03
import Solutions.Snaky21.Geometry
import Solutions.Snaky21.Certificate02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_card_192 : card_192 = combine (1, 5) [placed 0 (0, 1) card_9, placed 6 (2, 6) card_9, placed 0 (0, 0) card_186, placed 0 (1, 0) card_187, placed 0 (0, 1) card_191] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_192 : Valid card_192 := by
  rw [eq_card_192]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_186
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_187
  subst c
  exact placed_valid 0 (0, 1) valid_191

theorem eq_card_193 : card_193 = combine (1, 5) [placed 6 (1, 6) card_7, placed 3 (2, 2) card_26, placed 0 (0, 1) card_191] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_193 : Valid card_193 := by
  rw [eq_card_193]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 3 (2, 2) valid_26
  subst c
  exact placed_valid 0 (0, 1) valid_191

theorem eq_card_194 : card_194 = combine (1, 4) [placed 7 (1, 4) card_4, placed 4 (2, 0) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_194 : Valid card_194 := by
  rw [eq_card_194]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_4
  subst c
  exact placed_valid 4 (2, 0) valid_9

theorem eq_card_195 : card_195 = combine (1, 4) [placed 7 (1, 4) card_5, placed 0 (1, 0) card_7] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_195 : Valid card_195 := by
  rw [eq_card_195]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_7

theorem eq_card_196 : card_196 = combine (3, 0) [placed 2 (0, 1) card_5, placed 0 (1, 0) card_143] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_196 : Valid card_196 := by
  rw [eq_card_196]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_143

theorem eq_card_197 : card_197 = combine (4, 1) [placed 5 (0, 1) card_6, placed 0 (1, 0) card_8, placed 0 (1, 0) card_26, placed 0 (0, 0) card_196] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_197 : Valid card_197 := by
  rw [eq_card_197]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 1) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_26
  subst c
  exact placed_valid 0 (0, 0) valid_196

theorem eq_card_198 : card_198 = combine (1, 5) [placed 7 (1, 6) card_0, placed 2 (1, 5) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_198 : Valid card_198 := by
  rw [eq_card_198]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 6) valid_0
  subst c
  exact placed_valid 2 (1, 5) valid_6

theorem eq_card_199 : card_199 = combine (1, 1) [placed 3 (1, 0) card_0, placed 0 (0, 0) card_198] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_199 : Valid card_199 := by
  rw [eq_card_199]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 0) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_198

theorem eq_card_200 : card_200 = combine (1, 3) [placed 1 (0, 0) card_3, placed 7 (1, 4) card_3] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_200 : Valid card_200 := by
  rw [eq_card_200]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_3
  subst c
  exact placed_valid 7 (1, 4) valid_3

theorem eq_card_201 : card_201 = combine (3, 0) [placed 2 (0, 1) card_5, placed 3 (4, 0) card_146] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_201 : Valid card_201 := by
  rw [eq_card_201]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 3 (4, 0) valid_146

theorem eq_card_202 : card_202 = combine (3, 2) [placed 0 (0, 1) card_5, placed 4 (3, 0) card_27] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_202 : Valid card_202 := by
  rw [eq_card_202]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_27

theorem eq_card_203 : card_203 = combine (1, 3) [placed 5 (1, 4) card_5, placed 1 (0, 1) card_202] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_203 : Valid card_203 := by
  rw [eq_card_203]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_202

theorem eq_card_204 : card_204 = combine (2, 3) [placed 2 (1, 6) card_52, placed 1 (0, 2) card_203] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_204 : Valid card_204 := by
  rw [eq_card_204]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_52
  subst c
  exact placed_valid 1 (0, 2) valid_203

theorem eq_card_205 : card_205 = combine (1, 5) [placed 2 (1, 5) card_6, placed 4 (1, 2) card_23] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_205 : Valid card_205 := by
  rw [eq_card_205]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_6
  subst c
  exact placed_valid 4 (1, 2) valid_23

theorem eq_card_206 : card_206 = combine (1, 1) [placed 3 (1, 0) card_0, placed 0 (0, 0) card_205] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_206 : Valid card_206 := by
  rw [eq_card_206]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 0) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_205

theorem eq_card_207 : card_207 = combine (3, 1) [placed 2 (0, 1) card_5, placed 3 (4, 0) card_77] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_207 : Valid card_207 := by
  rw [eq_card_207]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 3 (4, 0) valid_77

theorem eq_card_208 : card_208 = combine (4, 0) [placed 2 (0, 1) card_4, placed 0 (1, 0) card_207] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_208 : Valid card_208 := by
  rw [eq_card_208]
  apply combination_rule (4, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_4
  subst c
  exact placed_valid 0 (1, 0) valid_207

theorem eq_card_209 : card_209 = combine (1, 4) [placed 7 (1, 5) card_0, placed 6 (1, 4) card_138] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_209 : Valid card_209 := by
  rw [eq_card_209]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact placed_valid 6 (1, 4) valid_138

theorem eq_card_210 : card_210 = combine (0, 0) [placed 7 (1, 4) card_1, placed 6 (4, 1) card_4] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_210 : Valid card_210 := by
  rw [eq_card_210]
  apply combination_rule (0, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_1
  subst c
  exact placed_valid 6 (4, 1) valid_4

theorem eq_card_211 : card_211 = combine (3, 5) [placed 6 (3, 6) card_7, placed 1 (2, 2) card_8, placed 0 (0, 1) card_151] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_211 : Valid card_211 := by
  rw [eq_card_211]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_8
  subst c
  exact placed_valid 0 (0, 1) valid_151

theorem eq_card_212 : card_212 = combine (1, 4) [placed 7 (1, 4) card_5, placed 0 (0, 1) card_76] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_212 : Valid card_212 := by
  rw [eq_card_212]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_76

theorem eq_card_213 : card_213 = combine (1, 4) [placed 4 (2, 0) card_53, placed 2 (1, 6) card_53, placed 5 (0, 4) card_212] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_213 : Valid card_213 := by
  rw [eq_card_213]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 0) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_53
  subst c
  exact placed_valid 5 (0, 4) valid_212

theorem eq_card_214 : card_214 = combine (3, 4) [placed 0 (0, 3) card_5, placed 2 (1, 6) card_213] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_214 : Valid card_214 := by
  rw [eq_card_214]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_5
  subst c
  exact placed_valid 2 (1, 6) valid_213

theorem eq_card_215 : card_215 = combine (3, 1) [placed 2 (0, 2) card_5, placed 4 (3, 0) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_215 : Valid card_215 := by
  rw [eq_card_215]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_11

theorem eq_card_216 : card_216 = combine (4, 3) [placed 0 (3, 0) card_52, placed 1 (0, 2) card_54] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_216 : Valid card_216 := by
  rw [eq_card_216]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_52
  subst c
  exact placed_valid 1 (0, 2) valid_54

theorem eq_card_217 : card_217 = combine (2, 4) [placed 4 (2, 1) card_21, placed 0 (1, 1) card_37, placed 5 (0, 5) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_217 : Valid card_217 := by
  rw [eq_card_217]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_37
  subst c
  exact placed_valid 5 (0, 5) valid_179

theorem eq_card_218 : card_218 = combine (1, 2) [placed 7 (1, 4) card_0, placed 2 (0, 4) card_83] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_218 : Valid card_218 := by
  rw [eq_card_218]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_0
  subst c
  exact placed_valid 2 (0, 4) valid_83

theorem eq_card_219 : card_219 = combine (1, 1) [placed 7 (1, 4) card_4, placed 6 (1, 5) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_219 : Valid card_219 := by
  rw [eq_card_219]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_4
  subst c
  exact placed_valid 6 (1, 5) valid_11

theorem eq_card_220 : card_220 = combine (3, 1) [placed 4 (4, 1) card_0, placed 5 (2, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_220 : Valid card_220 := by
  rw [eq_card_220]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 5 (2, 4) valid_5

theorem eq_card_221 : card_221 = combine (1, 3) [placed 3 (2, 0) card_5, placed 2 (0, 4) card_220] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_221 : Valid card_221 := by
  rw [eq_card_221]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (2, 0) valid_5
  subst c
  exact placed_valid 2 (0, 4) valid_220

theorem eq_card_222 : card_222 = combine (2, 1) [placed 3 (2, 1) card_5, placed 0 (0, 0) card_220] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_222 : Valid card_222 := by
  rw [eq_card_222]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (2, 1) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_220

theorem eq_card_223 : card_223 = combine (3, 0) [placed 2 (0, 1) card_5, placed 0 (3, 0) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_223 : Valid card_223 := by
  rw [eq_card_223]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact placed_valid 0 (3, 0) valid_6

theorem eq_card_224 : card_224 = combine (3, 1) [placed 0 (0, 1) card_5, placed 7 (3, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_224 : Valid card_224 := by
  rw [eq_card_224]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact placed_valid 7 (3, 4) valid_5

theorem eq_card_225 : card_225 = combine (1, 5) [placed 6 (1, 5) card_6, placed 3 (2, 2) card_26] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_225 : Valid card_225 := by
  rw [eq_card_225]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 5) valid_6
  subst c
  exact placed_valid 3 (2, 2) valid_26

theorem eq_card_226 : card_226 = combine (4, 1) [placed 4 (4, 1) card_4, placed 0 (1, 0) card_32] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_226 : Valid card_226 := by
  rw [eq_card_226]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_4
  subst c
  exact placed_valid 0 (1, 0) valid_32

theorem eq_card_227 : card_227 = combine (1, 4) [placed 1 (0, 0) card_0, placed 4 (2, 0) card_53] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_227 : Valid card_227 := by
  rw [eq_card_227]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_0
  subst c
  exact placed_valid 4 (2, 0) valid_53

theorem eq_card_228 : card_228 = combine (3, 2) [placed 5 (0, 3) card_52, placed 0 (1, 0) card_227] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_228 : Valid card_228 := by
  rw [eq_card_228]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_52
  subst c
  exact placed_valid 0 (1, 0) valid_227

theorem eq_card_229 : card_229 = combine (3, 3) [placed 0 (0, 2) card_5, placed 0 (0, 0) card_215] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_229 : Valid card_229 := by
  rw [eq_card_229]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_215

theorem eq_card_230 : card_230 = combine (4, 2) [placed 5 (0, 2) card_7, placed 1 (0, 1) card_9, placed 0 (1, 0) card_229] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_230 : Valid card_230 := by
  rw [eq_card_230]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_9
  subst c
  exact placed_valid 0 (1, 0) valid_229

theorem eq_card_231 : card_231 = combine (4, 3) [placed 0 (1, 2) card_8, placed 4 (4, 0) card_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_231 : Valid card_231 := by
  rw [eq_card_231]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_8
  subst c
  exact placed_valid 4 (4, 0) valid_55

theorem eq_card_232 : card_232 = combine (1, 4) [placed 7 (1, 4) card_5, placed 3 (2, 1) card_26] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_232 : Valid card_232 := by
  rw [eq_card_232]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 3 (2, 1) valid_26

theorem eq_card_233 : card_233 = combine (4, 1) [placed 1 (0, 1) card_6, placed 5 (1, 1) card_27] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_233 : Valid card_233 := by
  rw [eq_card_233]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_6
  subst c
  exact placed_valid 5 (1, 1) valid_27

theorem eq_card_234 : card_234 = combine (2, 1) [placed 5 (1, 4) card_5, placed 4 (2, 1) card_148] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_234 : Valid card_234 := by
  rw [eq_card_234]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 4 (2, 1) valid_148

theorem eq_card_235 : card_235 = combine (2, 1) [placed 5 (1, 4) card_5, placed 1 (0, 1) card_226] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_235 : Valid card_235 := by
  rw [eq_card_235]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_226

theorem eq_card_236 : card_236 = combine (1, 5) [placed 6 (1, 5) card_6, placed 1 (0, 2) card_32] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_236 : Valid card_236 := by
  rw [eq_card_236]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 5) valid_6
  subst c
  exact placed_valid 1 (0, 2) valid_32

theorem eq_card_237 : card_237 = combine (0, 1) [placed 6 (4, 2) card_0, placed 0 (0, 0) card_10] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_237 : Valid card_237 := by
  rw [eq_card_237]
  apply combination_rule (0, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_10

theorem eq_card_238 : card_238 = combine (2, 4) [placed 7 (2, 5) card_0, placed 5 (0, 5) card_133] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_238 : Valid card_238 := by
  rw [eq_card_238]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 5) valid_0
  subst c
  exact placed_valid 5 (0, 5) valid_133

theorem eq_card_239 : card_239 = combine (3, 1) [placed 6 (3, 5) card_11, placed 7 (4, 4) card_25] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_239 : Valid card_239 := by
  rw [eq_card_239]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 5) valid_11
  subst c
  exact placed_valid 7 (4, 4) valid_25

theorem eq_card_240 : card_240 = combine (2, 3) [placed 6 (4, 3) card_0, placed 4 (3, 0) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_240 : Valid card_240 := by
  rw [eq_card_240]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_0
  subst c
  exact placed_valid 4 (3, 0) valid_52

theorem eq_card_241 : card_241 = combine (2, 1) [placed 5 (1, 4) card_5, placed 4 (2, 1) card_91] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_241 : Valid card_241 := by
  rw [eq_card_241]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 4 (2, 1) valid_91

theorem eq_card_242 : card_242 = combine (4, 2) [placed 4 (4, 2) card_5, placed 0 (1, 0) card_69] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_242 : Valid card_242 := by
  rw [eq_card_242]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_69

theorem eq_card_243 : card_243 = combine (2, 2) [placed 4 (2, 1) card_10, placed 0 (0, 0) card_242] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_243 : Valid card_243 := by
  rw [eq_card_243]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_10
  subst c
  exact placed_valid 0 (0, 0) valid_242

theorem eq_card_244 : card_244 = combine (1, 4) [placed 4 (4, 3) card_5, placed 7 (1, 4) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_244 : Valid card_244 := by
  rw [eq_card_244]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_5
  subst c
  exact placed_valid 7 (1, 4) valid_5

theorem eq_card_245 : card_245 = combine (1, 4) [placed 5 (1, 4) card_5, placed 1 (0, 1) card_32] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_245 : Valid card_245 := by
  rw [eq_card_245]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_32

theorem eq_card_246 : card_246 = combine (1, 4) [placed 7 (1, 4) card_5, placed 1 (0, 1) card_25] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_246 : Valid card_246 := by
  rw [eq_card_246]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_25

theorem eq_card_247 : card_247 = combine (3, 4) [placed 0 (3, 0) card_11, placed 7 (4, 4) card_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_247 : Valid card_247 := by
  rw [eq_card_247]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_11
  subst c
  exact placed_valid 7 (4, 4) valid_35

theorem eq_card_248 : card_248 = combine (2, 5) [placed 6 (2, 6) card_44, placed 5 (0, 6) card_47, placed 0 (1, 1) card_127] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_248 : Valid card_248 := by
  rw [eq_card_248]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_47
  subst c
  exact placed_valid 0 (1, 1) valid_127

theorem eq_card_249 : card_249 = combine (4, 2) [placed 4 (4, 1) card_17, placed 7 (4, 4) card_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_249 : Valid card_249 := by
  rw [eq_card_249]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_17
  subst c
  exact placed_valid 7 (4, 4) valid_35

theorem eq_card_250 : card_250 = combine (1, 2) [placed 3 (1, 0) card_0, placed 0 (0, 0) card_195] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_250 : Valid card_250 := by
  rw [eq_card_250]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 0) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_195

theorem eq_card_251 : card_251 = combine (4, 2) [placed 0 (0, 1) card_4, placed 0 (1, 0) card_224] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_251 : Valid card_251 := by
  rw [eq_card_251]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_4
  subst c
  exact placed_valid 0 (1, 0) valid_224

theorem eq_card_252 : card_252 = combine (2, 4) [placed 2 (0, 6) card_55, placed 2 (0, 6) card_56, placed 1 (1, 2) card_91] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_252 : Valid card_252 := by
  rw [eq_card_252]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_55
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_56
  subst c
  exact placed_valid 1 (1, 2) valid_91

theorem eq_card_253 : card_253 = combine (4, 3) [placed 5 (0, 3) card_6, placed 1 (1, 2) card_18, placed 0 (0, 0) card_252] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_253 : Valid card_253 := by
  rw [eq_card_253]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_18
  subst c
  exact placed_valid 0 (0, 0) valid_252

theorem eq_card_254 : card_254 = combine (1, 5) [placed 4 (1, 1) card_11, placed 0 (0, 0) card_75, placed 6 (1, 5) card_103] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_254 : Valid card_254 := by
  rw [eq_card_254]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 1) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_75
  subst c
  exact placed_valid 6 (1, 5) valid_103

theorem eq_card_255 : card_255 = combine (3, 2) [placed 2 (0, 3) card_5, placed 0 (2, 0) card_254] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_255 : Valid card_255 := by
  rw [eq_card_255]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_5
  subst c
  exact placed_valid 0 (2, 0) valid_254

theorem block03_valid : Valid card_192 ∧ Valid card_193 ∧ Valid card_194 ∧ Valid card_195 ∧ Valid card_196 ∧ Valid card_197 ∧ Valid card_198 ∧ Valid card_199 ∧ Valid card_200 ∧ Valid card_201 ∧ Valid card_202 ∧ Valid card_203 ∧ Valid card_204 ∧ Valid card_205 ∧ Valid card_206 ∧ Valid card_207 ∧ Valid card_208 ∧ Valid card_209 ∧ Valid card_210 ∧ Valid card_211 ∧ Valid card_212 ∧ Valid card_213 ∧ Valid card_214 ∧ Valid card_215 ∧ Valid card_216 ∧ Valid card_217 ∧ Valid card_218 ∧ Valid card_219 ∧ Valid card_220 ∧ Valid card_221 ∧ Valid card_222 ∧ Valid card_223 ∧ Valid card_224 ∧ Valid card_225 ∧ Valid card_226 ∧ Valid card_227 ∧ Valid card_228 ∧ Valid card_229 ∧ Valid card_230 ∧ Valid card_231 ∧ Valid card_232 ∧ Valid card_233 ∧ Valid card_234 ∧ Valid card_235 ∧ Valid card_236 ∧ Valid card_237 ∧ Valid card_238 ∧ Valid card_239 ∧ Valid card_240 ∧ Valid card_241 ∧ Valid card_242 ∧ Valid card_243 ∧ Valid card_244 ∧ Valid card_245 ∧ Valid card_246 ∧ Valid card_247 ∧ Valid card_248 ∧ Valid card_249 ∧ Valid card_250 ∧ Valid card_251 ∧ Valid card_252 ∧ Valid card_253 ∧ Valid card_254 ∧ Valid card_255 ∧ True :=
  ⟨valid_192, valid_193, valid_194, valid_195, valid_196, valid_197, valid_198, valid_199, valid_200, valid_201, valid_202, valid_203, valid_204, valid_205, valid_206, valid_207, valid_208, valid_209, valid_210, valid_211, valid_212, valid_213, valid_214, valid_215, valid_216, valid_217, valid_218, valid_219, valid_220, valid_221, valid_222, valid_223, valid_224, valid_225, valid_226, valid_227, valid_228, valid_229, valid_230, valid_231, valid_232, valid_233, valid_234, valid_235, valid_236, valid_237, valid_238, valid_239, valid_240, valid_241, valid_242, valid_243, valid_244, valid_245, valid_246, valid_247, valid_248, valid_249, valid_250, valid_251, valid_252, valid_253, valid_254, valid_255, True.intro⟩

end OAI.Snaky21.Certificate
