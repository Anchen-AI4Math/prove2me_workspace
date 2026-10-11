import Definitions.Def_Snaky21Calc11
import Solutions.Snaky21.Geometry
import Solutions.Snaky21.Certificate11Part11

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem calc11_card_1272_eq : placed 0 (4, 2) card_55 = calc11_card_1272 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1273_eq : placed 4 (7, 0) card_659 = calc11_card_1273 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1274_eq : calc11_card_1273.required ∪ ∅ = calc11_set_1274 := by decide +kernel

theorem calc11_set_1275_eq : calc11_card_1273.envelope ∪ ∅ = calc11_set_1275 := by decide +kernel

theorem calc11_set_1276_eq : calc11_card_1272.required ∪ calc11_set_1274 = calc11_set_1276 := by decide +kernel

theorem calc11_set_1277_eq : calc11_card_1272.envelope ∪ calc11_set_1275 = calc11_set_1277 := by decide +kernel

theorem calc11_set_1278_eq : calc11_card_1273.envelope ∩ calc11_card_1272.envelope = calc11_set_1278 := by decide +kernel

theorem calc11_set_1279_eq : calc11_set_1276 ∪ calc11_set_1278 = calc11_set_1279 := by decide +kernel

theorem calc11_finishA_1280 : calc11_set_1279.erase (6, 4) = inline_848.required := by decide +kernel

theorem calc11_finishT_1280 : insert (6, 4) calc11_set_1277 = inline_848.envelope := by decide +kernel

theorem eq_inline_848 : inline_848 = combine (6, 4) [placed 0 (4, 2) card_55, placed 4 (7, 0) card_659] := by
  rw [calc11_card_1272_eq, calc11_card_1273_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1274_eq, calc11_set_1276_eq, calc11_set_1278_eq, calc11_set_1279_eq, calc11_finishA_1280]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1275_eq, calc11_set_1277_eq, calc11_finishT_1280]
  · decide +kernel

theorem valid_inline_848 : Valid inline_848 := by
  rw [eq_inline_848]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_55
  subst c
  exact placed_valid 4 (7, 0) valid_659

theorem calc11_card_1281_eq : placed 1 (3, 4) card_9 = calc11_card_1281 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1282_eq : placed 2 (4, 6) card_49 = calc11_card_1282 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1283_eq : placed 0 (3, 2) card_142 = calc11_card_1283 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1284_eq : inline_848.required ∪ ∅ = calc11_set_1284 := by decide +kernel

theorem calc11_set_1285_eq : inline_848.envelope ∪ ∅ = calc11_set_1285 := by decide +kernel

theorem calc11_set_1286_eq : calc11_card_1283.required ∪ calc11_set_1284 = calc11_set_1286 := by decide +kernel

theorem calc11_set_1287_eq : calc11_card_1283.envelope ∪ calc11_set_1285 = calc11_set_1287 := by decide +kernel

theorem calc11_set_1288_eq : calc11_card_1282.required ∪ calc11_set_1286 = calc11_set_1288 := by decide +kernel

theorem calc11_set_1289_eq : calc11_card_1282.envelope ∪ calc11_set_1287 = calc11_set_1289 := by decide +kernel

theorem calc11_set_1290_eq : calc11_card_1281.required ∪ calc11_set_1288 = calc11_set_1290 := by decide +kernel

theorem calc11_set_1291_eq : calc11_card_1281.envelope ∪ calc11_set_1289 = calc11_set_1291 := by decide +kernel

theorem calc11_set_1292_eq : inline_848.envelope ∩ calc11_card_1281.envelope = calc11_set_1292 := by decide +kernel

theorem calc11_set_1293_eq : calc11_card_1283.envelope ∩ calc11_set_1292 = calc11_set_1293 := by decide +kernel

theorem calc11_set_1294_eq : calc11_card_1282.envelope ∩ calc11_set_1293 = calc11_set_1294 := by decide +kernel

theorem calc11_set_1295_eq : calc11_set_1290 ∪ calc11_set_1294 = calc11_set_1295 := by decide +kernel

theorem calc11_finishA_1296 : calc11_set_1295.erase (7, 5) = card_716.required := by decide +kernel

theorem calc11_finishT_1296 : insert (7, 5) calc11_set_1291 = card_716.envelope := by decide +kernel

theorem eq_card_716 : card_716 = combine (7, 5) [placed 1 (3, 4) card_9, placed 2 (4, 6) card_49, placed 0 (3, 2) card_142, inline_848] := by
  rw [calc11_card_1281_eq, calc11_card_1282_eq, calc11_card_1283_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1284_eq, calc11_set_1286_eq, calc11_set_1288_eq, calc11_set_1290_eq, calc11_set_1292_eq, calc11_set_1293_eq, calc11_set_1294_eq, calc11_set_1295_eq, calc11_finishA_1296]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1285_eq, calc11_set_1287_eq, calc11_set_1289_eq, calc11_set_1291_eq, calc11_finishT_1296]
  · decide +kernel

theorem valid_716 : Valid card_716 := by
  rw [eq_card_716]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 6) valid_49
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_142
  subst c
  exact valid_inline_848


end OAI.Snaky21.Certificate
