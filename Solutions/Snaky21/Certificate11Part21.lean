import Definitions.Def_Snaky21Calc11
import Solutions.Snaky21.Geometry
import Solutions.Snaky21.Certificate11Part20

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem calc11_card_2169_eq : placed 2 (6, 12) card_459 = calc11_card_2169 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2170_eq : placed 7 (11, 9) card_579 = calc11_card_2170 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2171_eq : placed 6 (11, 12) card_581 = calc11_card_2171 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2172_eq : placed 2 (4, 11) card_654 = calc11_card_2172 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2173_eq : placed 0 (3, 3) card_661 = calc11_card_2173 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2174_eq : placed 6 (10, 12) card_677 = calc11_card_2174 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2175_eq : placed 7 (12, 11) card_682 = calc11_card_2175 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2176_eq : placed 2 (2, 13) card_694 = calc11_card_2176 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2177_eq : placed 0 (2, 2) card_696 = calc11_card_2177 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2178_eq : placed 6 (11, 12) card_698 = calc11_card_2178 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2179_eq : placed 0 (2, 2) card_709 = calc11_card_2179 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2180_eq : placed 0 (4, 3) card_710 = calc11_card_2180 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2181_eq : placed 5 (2, 12) card_715 = calc11_card_2181 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2182_eq : placed 7 (13, 12) card_717 = calc11_card_2182 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2183_eq : placed 0 (2, 2) card_718 = calc11_card_2183 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2184_eq : placed 6 (12, 15) card_724 = calc11_card_2184 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2185_eq : calc11_card_2184.required ∪ ∅ = calc11_set_2185 := by decide +kernel

theorem calc11_set_2186_eq : calc11_card_2184.envelope ∪ ∅ = calc11_set_2186 := by decide +kernel

theorem calc11_set_2187_eq : calc11_card_2183.required ∪ calc11_set_2185 = calc11_set_2187 := by decide +kernel

theorem calc11_set_2188_eq : calc11_card_2183.envelope ∪ calc11_set_2186 = calc11_set_2188 := by decide +kernel

theorem calc11_set_2189_eq : calc11_card_2182.required ∪ calc11_set_2187 = calc11_set_2189 := by decide +kernel

theorem calc11_set_2190_eq : calc11_card_2182.envelope ∪ calc11_set_2188 = calc11_set_2190 := by decide +kernel

theorem calc11_set_2191_eq : calc11_card_2181.required ∪ calc11_set_2189 = calc11_set_2191 := by decide +kernel

theorem calc11_set_2192_eq : calc11_card_2181.envelope ∪ calc11_set_2190 = calc11_set_2192 := by decide +kernel

theorem calc11_set_2193_eq : calc11_card_2180.required ∪ calc11_set_2191 = calc11_set_2193 := by decide +kernel

theorem calc11_set_2194_eq : calc11_card_2180.envelope ∪ calc11_set_2192 = calc11_set_2194 := by decide +kernel

theorem calc11_set_2195_eq : calc11_card_2179.required ∪ calc11_set_2193 = calc11_set_2195 := by decide +kernel

theorem calc11_set_2196_eq : calc11_card_2179.envelope ∪ calc11_set_2194 = calc11_set_2196 := by decide +kernel

theorem calc11_set_2197_eq : calc11_card_2178.required ∪ calc11_set_2195 = calc11_set_2197 := by decide +kernel

theorem calc11_set_2198_eq : calc11_card_2178.envelope ∪ calc11_set_2196 = calc11_set_2198 := by decide +kernel

theorem calc11_set_2199_eq : calc11_card_2177.required ∪ calc11_set_2197 = calc11_set_2199 := by decide +kernel

theorem calc11_set_2200_eq : calc11_card_2177.envelope ∪ calc11_set_2198 = calc11_set_2200 := by decide +kernel

theorem calc11_set_2201_eq : calc11_card_2176.required ∪ calc11_set_2199 = calc11_set_2201 := by decide +kernel

theorem calc11_set_2202_eq : calc11_card_2176.envelope ∪ calc11_set_2200 = calc11_set_2202 := by decide +kernel

theorem calc11_set_2203_eq : calc11_card_2175.required ∪ calc11_set_2201 = calc11_set_2203 := by decide +kernel

theorem calc11_set_2204_eq : calc11_card_2175.envelope ∪ calc11_set_2202 = calc11_set_2204 := by decide +kernel

theorem calc11_set_2205_eq : calc11_card_2174.required ∪ calc11_set_2203 = calc11_set_2205 := by decide +kernel

theorem calc11_set_2206_eq : calc11_card_2174.envelope ∪ calc11_set_2204 = calc11_set_2206 := by decide +kernel

theorem calc11_set_2207_eq : calc11_card_2173.required ∪ calc11_set_2205 = calc11_set_2207 := by decide +kernel

theorem calc11_set_2208_eq : calc11_card_2173.envelope ∪ calc11_set_2206 = calc11_set_2208 := by decide +kernel

theorem calc11_set_2209_eq : calc11_card_2172.required ∪ calc11_set_2207 = calc11_set_2209 := by decide +kernel

theorem calc11_set_2210_eq : calc11_card_2172.envelope ∪ calc11_set_2208 = calc11_set_2210 := by decide +kernel

theorem calc11_set_2211_eq : calc11_card_2171.required ∪ calc11_set_2209 = calc11_set_2211 := by decide +kernel

theorem calc11_set_2212_eq : calc11_card_2171.envelope ∪ calc11_set_2210 = calc11_set_2212 := by decide +kernel

theorem calc11_set_2213_eq : calc11_card_2170.required ∪ calc11_set_2211 = calc11_set_2213 := by decide +kernel

theorem calc11_set_2214_eq : calc11_card_2170.envelope ∪ calc11_set_2212 = calc11_set_2214 := by decide +kernel

theorem calc11_set_2215_eq : calc11_card_2169.required ∪ calc11_set_2213 = calc11_set_2215 := by decide +kernel

theorem calc11_set_2216_eq : calc11_card_2169.envelope ∪ calc11_set_2214 = calc11_set_2216 := by decide +kernel

theorem calc11_set_2217_eq : calc11_card_2184.envelope ∩ calc11_card_2169.envelope = calc11_set_2217 := by decide +kernel

theorem calc11_set_2218_eq : calc11_card_2183.envelope ∩ calc11_set_2217 = calc11_set_2218 := by decide +kernel

theorem calc11_set_2219_eq : calc11_card_2182.envelope ∩ calc11_set_2218 = calc11_set_2219 := by decide +kernel

theorem calc11_set_2220_eq : calc11_card_2181.envelope ∩ calc11_set_2219 = calc11_set_2220 := by decide +kernel

theorem calc11_set_2221_eq : calc11_card_2180.envelope ∩ calc11_set_2220 = calc11_set_2221 := by decide +kernel

theorem calc11_set_2222_eq : calc11_card_2179.envelope ∩ calc11_set_2221 = calc11_set_2222 := by decide +kernel

theorem calc11_set_2223_eq : calc11_card_2178.envelope ∩ calc11_set_2222 = calc11_set_2223 := by decide +kernel

theorem calc11_set_2224_eq : calc11_card_2177.envelope ∩ calc11_set_2223 = calc11_set_2224 := by decide +kernel

theorem calc11_set_2225_eq : calc11_card_2176.envelope ∩ calc11_set_2224 = calc11_set_2225 := by decide +kernel

theorem calc11_set_2226_eq : calc11_card_2175.envelope ∩ calc11_set_2225 = calc11_set_2226 := by decide +kernel

theorem calc11_set_2227_eq : calc11_card_2174.envelope ∩ calc11_set_2226 = calc11_set_2227 := by decide +kernel

theorem calc11_set_2228_eq : calc11_card_2173.envelope ∩ calc11_set_2227 = calc11_set_2228 := by decide +kernel

theorem calc11_set_2229_eq : calc11_card_2172.envelope ∩ calc11_set_2228 = calc11_set_2229 := by decide +kernel

theorem calc11_set_2230_eq : calc11_card_2171.envelope ∩ calc11_set_2229 = calc11_set_2230 := by decide +kernel

theorem calc11_set_2231_eq : calc11_card_2170.envelope ∩ calc11_set_2230 = calc11_set_2231 := by decide +kernel

theorem calc11_set_2232_eq : calc11_set_2215 ∪ calc11_set_2231 = calc11_set_2232 := by decide +kernel

theorem calc11_finishA_2233 : calc11_set_2232.erase (7, 8) = card_725.required := by decide +kernel

theorem calc11_finishT_2233 : insert (7, 8) calc11_set_2216 = card_725.envelope := by decide +kernel

theorem eq_card_725 : card_725 = combine (7, 8) [placed 2 (6, 12) card_459, placed 7 (11, 9) card_579, placed 6 (11, 12) card_581, placed 2 (4, 11) card_654, placed 0 (3, 3) card_661, placed 6 (10, 12) card_677, placed 7 (12, 11) card_682, placed 2 (2, 13) card_694, placed 0 (2, 2) card_696, placed 6 (11, 12) card_698, placed 0 (2, 2) card_709, placed 0 (4, 3) card_710, placed 5 (2, 12) card_715, placed 7 (13, 12) card_717, placed 0 (2, 2) card_718, placed 6 (12, 15) card_724] := by
  rw [calc11_card_2169_eq, calc11_card_2170_eq, calc11_card_2171_eq, calc11_card_2172_eq, calc11_card_2173_eq, calc11_card_2174_eq, calc11_card_2175_eq, calc11_card_2176_eq, calc11_card_2177_eq, calc11_card_2178_eq, calc11_card_2179_eq, calc11_card_2180_eq, calc11_card_2181_eq, calc11_card_2182_eq, calc11_card_2183_eq, calc11_card_2184_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2185_eq, calc11_set_2187_eq, calc11_set_2189_eq, calc11_set_2191_eq, calc11_set_2193_eq, calc11_set_2195_eq, calc11_set_2197_eq, calc11_set_2199_eq, calc11_set_2201_eq, calc11_set_2203_eq, calc11_set_2205_eq, calc11_set_2207_eq, calc11_set_2209_eq, calc11_set_2211_eq, calc11_set_2213_eq, calc11_set_2215_eq, calc11_set_2217_eq, calc11_set_2218_eq, calc11_set_2219_eq, calc11_set_2220_eq, calc11_set_2221_eq, calc11_set_2222_eq, calc11_set_2223_eq, calc11_set_2224_eq, calc11_set_2225_eq, calc11_set_2226_eq, calc11_set_2227_eq, calc11_set_2228_eq, calc11_set_2229_eq, calc11_set_2230_eq, calc11_set_2231_eq, calc11_set_2232_eq, calc11_finishA_2233]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2186_eq, calc11_set_2188_eq, calc11_set_2190_eq, calc11_set_2192_eq, calc11_set_2194_eq, calc11_set_2196_eq, calc11_set_2198_eq, calc11_set_2200_eq, calc11_set_2202_eq, calc11_set_2204_eq, calc11_set_2206_eq, calc11_set_2208_eq, calc11_set_2210_eq, calc11_set_2212_eq, calc11_set_2214_eq, calc11_set_2216_eq, calc11_finishT_2233]
  · decide +kernel

theorem valid_725 : Valid card_725 := by
  rw [eq_card_725]
  apply combination_rule (7, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 12) valid_459
  rcases hc with rfl | hc
  · exact placed_valid 7 (11, 9) valid_579
  rcases hc with rfl | hc
  · exact placed_valid 6 (11, 12) valid_581
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 11) valid_654
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_661
  rcases hc with rfl | hc
  · exact placed_valid 6 (10, 12) valid_677
  rcases hc with rfl | hc
  · exact placed_valid 7 (12, 11) valid_682
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 13) valid_694
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_696
  rcases hc with rfl | hc
  · exact placed_valid 6 (11, 12) valid_698
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_709
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_710
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 12) valid_715
  rcases hc with rfl | hc
  · exact placed_valid 7 (13, 12) valid_717
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_718
  subst c
  exact placed_valid 6 (12, 15) valid_724


end OAI.Snaky21.Certificate
