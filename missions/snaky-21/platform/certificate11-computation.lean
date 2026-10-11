import Definitions.Def_Snaky21Calc11
import Solutions.Snaky21.Geometry
import Solutions.Snaky21.Certificate10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem calc11_card_0_eq : placed 3 (5, 4) card_28 = calc11_card_0 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1_eq : placed 0 (1, 3) card_58 = calc11_card_1 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2_eq : placed 0 (1, 2) card_306 = calc11_card_2 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_3_eq : calc11_card_2.required ∪ ∅ = calc11_set_3 := by decide +kernel

theorem calc11_set_4_eq : calc11_card_2.envelope ∪ ∅ = calc11_set_4 := by decide +kernel

theorem calc11_set_5_eq : calc11_card_1.required ∪ calc11_set_3 = calc11_set_5 := by decide +kernel

theorem calc11_set_6_eq : calc11_card_1.envelope ∪ calc11_set_4 = calc11_set_6 := by decide +kernel

theorem calc11_set_7_eq : calc11_card_0.required ∪ calc11_set_5 = calc11_set_7 := by decide +kernel

theorem calc11_set_8_eq : calc11_card_0.envelope ∪ calc11_set_6 = calc11_set_8 := by decide +kernel

theorem calc11_set_9_eq : calc11_card_2.envelope ∩ calc11_card_0.envelope = calc11_set_9 := by decide +kernel

theorem calc11_set_10_eq : calc11_card_1.envelope ∩ calc11_set_9 = calc11_set_10 := by decide +kernel

theorem calc11_set_11_eq : calc11_set_7 ∪ calc11_set_10 = calc11_set_11 := by decide +kernel

theorem calc11_finishA_12 : calc11_set_11.erase (4, 6) = inline_794.required := by decide +kernel

theorem calc11_finishT_12 : insert (4, 6) calc11_set_8 = inline_794.envelope := by decide +kernel

theorem eq_inline_794 : inline_794 = combine (4, 6) [placed 3 (5, 4) card_28, placed 0 (1, 3) card_58, placed 0 (1, 2) card_306] := by
  rw [calc11_card_0_eq, calc11_card_1_eq, calc11_card_2_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_3_eq, calc11_set_5_eq, calc11_set_7_eq, calc11_set_9_eq, calc11_set_10_eq, calc11_set_11_eq, calc11_finishA_12]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_4_eq, calc11_set_6_eq, calc11_set_8_eq, calc11_finishT_12]
  · decide +kernel

theorem valid_inline_794 : Valid inline_794 := by
  rw [eq_inline_794]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 4) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_58
  subst c
  exact placed_valid 0 (1, 2) valid_306

theorem calc11_card_13_eq : placed 6 (5, 5) card_2 = calc11_card_13 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_14_eq : placed 0 (4, 2) card_52 = calc11_card_14 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_15_eq : calc11_card_14.required ∪ ∅ = calc11_set_15 := by decide +kernel

theorem calc11_set_16_eq : calc11_card_14.envelope ∪ ∅ = calc11_set_16 := by decide +kernel

theorem calc11_set_17_eq : calc11_card_13.required ∪ calc11_set_15 = calc11_set_17 := by decide +kernel

theorem calc11_set_18_eq : calc11_card_13.envelope ∪ calc11_set_16 = calc11_set_18 := by decide +kernel

theorem calc11_set_19_eq : calc11_card_14.envelope ∩ calc11_card_13.envelope = calc11_set_19 := by decide +kernel

theorem calc11_set_20_eq : calc11_set_17 ∪ calc11_set_19 = calc11_set_20 := by decide +kernel

theorem calc11_finishA_21 : calc11_set_20.erase (5, 5) = inline_795.required := by decide +kernel

theorem calc11_finishT_21 : insert (5, 5) calc11_set_18 = inline_795.envelope := by decide +kernel

theorem eq_inline_795 : inline_795 = combine (5, 5) [placed 6 (5, 5) card_2, placed 0 (4, 2) card_52] := by
  rw [calc11_card_13_eq, calc11_card_14_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_15_eq, calc11_set_17_eq, calc11_set_19_eq, calc11_set_20_eq, calc11_finishA_21]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_16_eq, calc11_set_18_eq, calc11_finishT_21]
  · decide +kernel

theorem valid_inline_795 : Valid inline_795 := by
  rw [eq_inline_795]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 5) valid_2
  subst c
  exact placed_valid 0 (4, 2) valid_52

theorem calc11_card_22_eq : placed 6 (5, 5) card_2 = calc11_card_22 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_23_eq : placed 6 (5, 6) card_10 = calc11_card_23 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_24_eq : calc11_card_23.required ∪ ∅ = calc11_set_24 := by decide +kernel

theorem calc11_set_25_eq : calc11_card_23.envelope ∪ ∅ = calc11_set_25 := by decide +kernel

theorem calc11_set_26_eq : calc11_card_22.required ∪ calc11_set_24 = calc11_set_26 := by decide +kernel

theorem calc11_set_27_eq : calc11_card_22.envelope ∪ calc11_set_25 = calc11_set_27 := by decide +kernel

theorem calc11_set_28_eq : calc11_card_23.envelope ∩ calc11_card_22.envelope = calc11_set_28 := by decide +kernel

theorem calc11_set_29_eq : calc11_set_26 ∪ calc11_set_28 = calc11_set_29 := by decide +kernel

theorem calc11_finishA_30 : calc11_set_29.erase (5, 5) = inline_796.required := by decide +kernel

theorem calc11_finishT_30 : insert (5, 5) calc11_set_27 = inline_796.envelope := by decide +kernel

theorem eq_inline_796 : inline_796 = combine (5, 5) [placed 6 (5, 5) card_2, placed 6 (5, 6) card_10] := by
  rw [calc11_card_22_eq, calc11_card_23_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_24_eq, calc11_set_26_eq, calc11_set_28_eq, calc11_set_29_eq, calc11_finishA_30]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_25_eq, calc11_set_27_eq, calc11_finishT_30]
  · decide +kernel

theorem valid_inline_796 : Valid inline_796 := by
  rw [eq_inline_796]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 5) valid_2
  subst c
  exact placed_valid 6 (5, 6) valid_10

theorem calc11_card_31_eq : placed 3 (5, 3) card_25 = calc11_card_31 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_32_eq : placed 7 (5, 6) card_78 = calc11_card_32 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_33_eq : calc11_card_32.required ∪ ∅ = calc11_set_33 := by decide +kernel

theorem calc11_set_34_eq : calc11_card_32.envelope ∪ ∅ = calc11_set_34 := by decide +kernel

theorem calc11_set_35_eq : calc11_card_31.required ∪ calc11_set_33 = calc11_set_35 := by decide +kernel

theorem calc11_set_36_eq : calc11_card_31.envelope ∪ calc11_set_34 = calc11_set_36 := by decide +kernel

theorem calc11_set_37_eq : calc11_card_32.envelope ∩ calc11_card_31.envelope = calc11_set_37 := by decide +kernel

theorem calc11_set_38_eq : calc11_set_35 ∪ calc11_set_37 = calc11_set_38 := by decide +kernel

theorem calc11_finishA_39 : calc11_set_38.erase (4, 6) = inline_797.required := by decide +kernel

theorem calc11_finishT_39 : insert (4, 6) calc11_set_36 = inline_797.envelope := by decide +kernel

theorem eq_inline_797 : inline_797 = combine (4, 6) [placed 3 (5, 3) card_25, placed 7 (5, 6) card_78] := by
  rw [calc11_card_31_eq, calc11_card_32_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_33_eq, calc11_set_35_eq, calc11_set_37_eq, calc11_set_38_eq, calc11_finishA_39]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_34_eq, calc11_set_36_eq, calc11_finishT_39]
  · decide +kernel

theorem valid_inline_797 : Valid inline_797 := by
  rw [eq_inline_797]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_25
  subst c
  exact placed_valid 7 (5, 6) valid_78

theorem calc11_card_40_eq : placed 2 (1, 6) card_516 = calc11_card_40 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_41_eq : inline_797.required ∪ ∅ = calc11_set_41 := by decide +kernel

theorem calc11_set_42_eq : inline_797.envelope ∪ ∅ = calc11_set_42 := by decide +kernel

theorem calc11_set_43_eq : inline_796.required ∪ calc11_set_41 = calc11_set_43 := by decide +kernel

theorem calc11_set_44_eq : inline_796.envelope ∪ calc11_set_42 = calc11_set_44 := by decide +kernel

theorem calc11_set_45_eq : inline_795.required ∪ calc11_set_43 = calc11_set_45 := by decide +kernel

theorem calc11_set_46_eq : inline_795.envelope ∪ calc11_set_44 = calc11_set_46 := by decide +kernel

theorem calc11_set_47_eq : calc11_card_40.required ∪ calc11_set_45 = calc11_set_47 := by decide +kernel

theorem calc11_set_48_eq : calc11_card_40.envelope ∪ calc11_set_46 = calc11_set_48 := by decide +kernel

theorem calc11_set_49_eq : inline_797.envelope ∩ calc11_card_40.envelope = calc11_set_49 := by decide +kernel

theorem calc11_set_50_eq : inline_796.envelope ∩ calc11_set_49 = calc11_set_50 := by decide +kernel

theorem calc11_set_51_eq : inline_795.envelope ∩ calc11_set_50 = calc11_set_51 := by decide +kernel

theorem calc11_set_52_eq : calc11_set_47 ∪ calc11_set_51 = calc11_set_52 := by decide +kernel

theorem calc11_finishA_53 : calc11_set_52.erase (4, 3) = inline_798.required := by decide +kernel

theorem calc11_finishT_53 : insert (4, 3) calc11_set_48 = inline_798.envelope := by decide +kernel

theorem eq_inline_798 : inline_798 = combine (4, 3) [placed 2 (1, 6) card_516, inline_795, inline_796, inline_797] := by
  rw [calc11_card_40_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_41_eq, calc11_set_43_eq, calc11_set_45_eq, calc11_set_47_eq, calc11_set_49_eq, calc11_set_50_eq, calc11_set_51_eq, calc11_set_52_eq, calc11_finishA_53]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_42_eq, calc11_set_44_eq, calc11_set_46_eq, calc11_set_48_eq, calc11_finishT_53]
  · decide +kernel

theorem valid_inline_798 : Valid inline_798 := by
  rw [eq_inline_798]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_516
  rcases hc with rfl | hc
  · exact valid_inline_795
  rcases hc with rfl | hc
  · exact valid_inline_796
  subst c
  exact valid_inline_797

theorem calc11_card_54_eq : placed 5 (1, 5) card_30 = calc11_card_54 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_55_eq : placed 0 (0, 0) card_703 = calc11_card_55 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_56_eq : inline_798.required ∪ ∅ = calc11_set_56 := by decide +kernel

theorem calc11_set_57_eq : inline_798.envelope ∪ ∅ = calc11_set_57 := by decide +kernel

theorem calc11_set_58_eq : calc11_card_55.required ∪ calc11_set_56 = calc11_set_58 := by decide +kernel

theorem calc11_set_59_eq : calc11_card_55.envelope ∪ calc11_set_57 = calc11_set_59 := by decide +kernel

theorem calc11_set_60_eq : inline_794.required ∪ calc11_set_58 = calc11_set_60 := by decide +kernel

theorem calc11_set_61_eq : inline_794.envelope ∪ calc11_set_59 = calc11_set_61 := by decide +kernel

theorem calc11_set_62_eq : calc11_card_54.required ∪ calc11_set_60 = calc11_set_62 := by decide +kernel

theorem calc11_set_63_eq : calc11_card_54.envelope ∪ calc11_set_61 = calc11_set_63 := by decide +kernel

theorem calc11_set_64_eq : inline_798.envelope ∩ calc11_card_54.envelope = calc11_set_64 := by decide +kernel

theorem calc11_set_65_eq : calc11_card_55.envelope ∩ calc11_set_64 = calc11_set_65 := by decide +kernel

theorem calc11_set_66_eq : inline_794.envelope ∩ calc11_set_65 = calc11_set_66 := by decide +kernel

theorem calc11_set_67_eq : calc11_set_62 ∪ calc11_set_66 = calc11_set_67 := by decide +kernel

theorem calc11_finishA_68 : calc11_set_67.erase (4, 5) = inline_799.required := by decide +kernel

theorem calc11_finishT_68 : insert (4, 5) calc11_set_63 = inline_799.envelope := by decide +kernel

theorem eq_inline_799 : inline_799 = combine (4, 5) [placed 5 (1, 5) card_30, inline_794, placed 0 (0, 0) card_703, inline_798] := by
  rw [calc11_card_54_eq, calc11_card_55_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_56_eq, calc11_set_58_eq, calc11_set_60_eq, calc11_set_62_eq, calc11_set_64_eq, calc11_set_65_eq, calc11_set_66_eq, calc11_set_67_eq, calc11_finishA_68]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_57_eq, calc11_set_59_eq, calc11_set_61_eq, calc11_set_63_eq, calc11_finishT_68]
  · decide +kernel

theorem valid_inline_799 : Valid inline_799 := by
  rw [eq_inline_799]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_30
  rcases hc with rfl | hc
  · exact valid_inline_794
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_703
  subst c
  exact valid_inline_798

theorem calc11_card_69_eq : placed 1 (0, 4) card_22 = calc11_card_69 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_70_eq : placed 2 (0, 6) card_400 = calc11_card_70 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_71_eq : inline_799.required ∪ ∅ = calc11_set_71 := by decide +kernel

theorem calc11_set_72_eq : inline_799.envelope ∪ ∅ = calc11_set_72 := by decide +kernel

theorem calc11_set_73_eq : calc11_card_70.required ∪ calc11_set_71 = calc11_set_73 := by decide +kernel

theorem calc11_set_74_eq : calc11_card_70.envelope ∪ calc11_set_72 = calc11_set_74 := by decide +kernel

theorem calc11_set_75_eq : calc11_card_69.required ∪ calc11_set_73 = calc11_set_75 := by decide +kernel

theorem calc11_set_76_eq : calc11_card_69.envelope ∪ calc11_set_74 = calc11_set_76 := by decide +kernel

theorem calc11_set_77_eq : inline_799.envelope ∩ calc11_card_69.envelope = calc11_set_77 := by decide +kernel

theorem calc11_set_78_eq : calc11_card_70.envelope ∩ calc11_set_77 = calc11_set_78 := by decide +kernel

theorem calc11_set_79_eq : calc11_set_75 ∪ calc11_set_78 = calc11_set_79 := by decide +kernel

theorem calc11_finishA_80 : calc11_set_79.erase (4, 4) = card_704.required := by decide +kernel

theorem calc11_finishT_80 : insert (4, 4) calc11_set_76 = card_704.envelope := by decide +kernel

theorem eq_card_704 : card_704 = combine (4, 4) [placed 1 (0, 4) card_22, placed 2 (0, 6) card_400, inline_799] := by
  rw [calc11_card_69_eq, calc11_card_70_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_71_eq, calc11_set_73_eq, calc11_set_75_eq, calc11_set_77_eq, calc11_set_78_eq, calc11_set_79_eq, calc11_finishA_80]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_72_eq, calc11_set_74_eq, calc11_set_76_eq, calc11_finishT_80]
  · decide +kernel

theorem valid_704 : Valid card_704 := by
  rw [eq_card_704]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_400
  subst c
  exact valid_inline_799

theorem calc11_card_81_eq : placed 6 (6, 8) card_14 = calc11_card_81 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_82_eq : placed 2 (2, 7) card_79 = calc11_card_82 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_83_eq : placed 1 (3, 3) card_181 = calc11_card_83 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_84_eq : placed 4 (6, 2) card_189 = calc11_card_84 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_85_eq : placed 2 (4, 8) card_367 = calc11_card_85 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_86_eq : placed 1 (3, 3) card_474 = calc11_card_86 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_87_eq : calc11_card_86.required ∪ ∅ = calc11_set_87 := by decide +kernel

theorem calc11_set_88_eq : calc11_card_86.envelope ∪ ∅ = calc11_set_88 := by decide +kernel

theorem calc11_set_89_eq : calc11_card_85.required ∪ calc11_set_87 = calc11_set_89 := by decide +kernel

theorem calc11_set_90_eq : calc11_card_85.envelope ∪ calc11_set_88 = calc11_set_90 := by decide +kernel

theorem calc11_set_91_eq : calc11_card_84.required ∪ calc11_set_89 = calc11_set_91 := by decide +kernel

theorem calc11_set_92_eq : calc11_card_84.envelope ∪ calc11_set_90 = calc11_set_92 := by decide +kernel

theorem calc11_set_93_eq : calc11_card_83.required ∪ calc11_set_91 = calc11_set_93 := by decide +kernel

theorem calc11_set_94_eq : calc11_card_83.envelope ∪ calc11_set_92 = calc11_set_94 := by decide +kernel

theorem calc11_set_95_eq : calc11_card_82.required ∪ calc11_set_93 = calc11_set_95 := by decide +kernel

theorem calc11_set_96_eq : calc11_card_82.envelope ∪ calc11_set_94 = calc11_set_96 := by decide +kernel

theorem calc11_set_97_eq : calc11_card_81.required ∪ calc11_set_95 = calc11_set_97 := by decide +kernel

theorem calc11_set_98_eq : calc11_card_81.envelope ∪ calc11_set_96 = calc11_set_98 := by decide +kernel

theorem calc11_set_99_eq : calc11_card_86.envelope ∩ calc11_card_81.envelope = calc11_set_99 := by decide +kernel

theorem calc11_set_100_eq : calc11_card_85.envelope ∩ calc11_set_99 = calc11_set_100 := by decide +kernel

theorem calc11_set_101_eq : calc11_card_84.envelope ∩ calc11_set_100 = calc11_set_101 := by decide +kernel

theorem calc11_set_102_eq : calc11_card_83.envelope ∩ calc11_set_101 = calc11_set_102 := by decide +kernel

theorem calc11_set_103_eq : calc11_card_82.envelope ∩ calc11_set_102 = calc11_set_103 := by decide +kernel

theorem calc11_set_104_eq : calc11_set_97 ∪ calc11_set_103 = calc11_set_104 := by decide +kernel

theorem calc11_finishA_105 : calc11_set_104.erase (5, 6) = inline_800.required := by decide +kernel

theorem calc11_finishT_105 : insert (5, 6) calc11_set_98 = inline_800.envelope := by decide +kernel

theorem eq_inline_800 : inline_800 = combine (5, 6) [placed 6 (6, 8) card_14, placed 2 (2, 7) card_79, placed 1 (3, 3) card_181, placed 4 (6, 2) card_189, placed 2 (4, 8) card_367, placed 1 (3, 3) card_474] := by
  rw [calc11_card_81_eq, calc11_card_82_eq, calc11_card_83_eq, calc11_card_84_eq, calc11_card_85_eq, calc11_card_86_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_87_eq, calc11_set_89_eq, calc11_set_91_eq, calc11_set_93_eq, calc11_set_95_eq, calc11_set_97_eq, calc11_set_99_eq, calc11_set_100_eq, calc11_set_101_eq, calc11_set_102_eq, calc11_set_103_eq, calc11_set_104_eq, calc11_finishA_105]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_88_eq, calc11_set_90_eq, calc11_set_92_eq, calc11_set_94_eq, calc11_set_96_eq, calc11_set_98_eq, calc11_finishT_105]
  · decide +kernel

theorem valid_inline_800 : Valid inline_800 := by
  rw [eq_inline_800]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_367
  subst c
  exact placed_valid 1 (3, 3) valid_474

theorem calc11_card_106_eq : placed 2 (2, 8) card_59 = calc11_card_106 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_107_eq : placed 5 (1, 5) card_105 = calc11_card_107 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_108_eq : placed 4 (6, 1) card_323 = calc11_card_108 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_109_eq : inline_800.required ∪ ∅ = calc11_set_109 := by decide +kernel

theorem calc11_set_110_eq : inline_800.envelope ∪ ∅ = calc11_set_110 := by decide +kernel

theorem calc11_set_111_eq : calc11_card_108.required ∪ calc11_set_109 = calc11_set_111 := by decide +kernel

theorem calc11_set_112_eq : calc11_card_108.envelope ∪ calc11_set_110 = calc11_set_112 := by decide +kernel

theorem calc11_set_113_eq : calc11_card_107.required ∪ calc11_set_111 = calc11_set_113 := by decide +kernel

theorem calc11_set_114_eq : calc11_card_107.envelope ∪ calc11_set_112 = calc11_set_114 := by decide +kernel

theorem calc11_set_115_eq : calc11_card_106.required ∪ calc11_set_113 = calc11_set_115 := by decide +kernel

theorem calc11_set_116_eq : calc11_card_106.envelope ∪ calc11_set_114 = calc11_set_116 := by decide +kernel

theorem calc11_set_117_eq : inline_800.envelope ∩ calc11_card_106.envelope = calc11_set_117 := by decide +kernel

theorem calc11_set_118_eq : calc11_card_108.envelope ∩ calc11_set_117 = calc11_set_118 := by decide +kernel

theorem calc11_set_119_eq : calc11_card_107.envelope ∩ calc11_set_118 = calc11_set_119 := by decide +kernel

theorem calc11_set_120_eq : calc11_set_115 ∪ calc11_set_119 = calc11_set_120 := by decide +kernel

theorem calc11_finishA_121 : calc11_set_120.erase (5, 5) = inline_801.required := by decide +kernel

theorem calc11_finishT_121 : insert (5, 5) calc11_set_116 = inline_801.envelope := by decide +kernel

theorem eq_inline_801 : inline_801 = combine (5, 5) [placed 2 (2, 8) card_59, placed 5 (1, 5) card_105, placed 4 (6, 1) card_323, inline_800] := by
  rw [calc11_card_106_eq, calc11_card_107_eq, calc11_card_108_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_109_eq, calc11_set_111_eq, calc11_set_113_eq, calc11_set_115_eq, calc11_set_117_eq, calc11_set_118_eq, calc11_set_119_eq, calc11_set_120_eq, calc11_finishA_121]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_110_eq, calc11_set_112_eq, calc11_set_114_eq, calc11_set_116_eq, calc11_finishT_121]
  · decide +kernel

theorem valid_inline_801 : Valid inline_801 := by
  rw [eq_inline_801]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_105
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_323
  subst c
  exact valid_inline_800

theorem calc11_card_122_eq : placed 6 (5, 7) card_52 = calc11_card_122 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_123_eq : placed 4 (6, 2) card_242 = calc11_card_123 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_124_eq : calc11_card_123.required ∪ ∅ = calc11_set_124 := by decide +kernel

theorem calc11_set_125_eq : calc11_card_123.envelope ∪ ∅ = calc11_set_125 := by decide +kernel

theorem calc11_set_126_eq : calc11_card_122.required ∪ calc11_set_124 = calc11_set_126 := by decide +kernel

theorem calc11_set_127_eq : calc11_card_122.envelope ∪ calc11_set_125 = calc11_set_127 := by decide +kernel

theorem calc11_set_128_eq : calc11_card_123.envelope ∩ calc11_card_122.envelope = calc11_set_128 := by decide +kernel

theorem calc11_set_129_eq : calc11_set_126 ∪ calc11_set_128 = calc11_set_129 := by decide +kernel

theorem calc11_finishA_130 : calc11_set_129.erase (4, 4) = inline_802.required := by decide +kernel

theorem calc11_finishT_130 : insert (4, 4) calc11_set_127 = inline_802.envelope := by decide +kernel

theorem eq_inline_802 : inline_802 = combine (4, 4) [placed 6 (5, 7) card_52, placed 4 (6, 2) card_242] := by
  rw [calc11_card_122_eq, calc11_card_123_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_124_eq, calc11_set_126_eq, calc11_set_128_eq, calc11_set_129_eq, calc11_finishA_130]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_125_eq, calc11_set_127_eq, calc11_finishT_130]
  · decide +kernel

theorem valid_inline_802 : Valid inline_802 := by
  rw [eq_inline_802]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_52
  subst c
  exact placed_valid 4 (6, 2) valid_242

theorem calc11_card_131_eq : placed 2 (2, 7) card_79 = calc11_card_131 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_132_eq : placed 4 (6, 2) card_243 = calc11_card_132 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_133_eq : placed 4 (8, 1) card_518 = calc11_card_133 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_134_eq : inline_802.required ∪ ∅ = calc11_set_134 := by decide +kernel

theorem calc11_set_135_eq : inline_802.envelope ∪ ∅ = calc11_set_135 := by decide +kernel

theorem calc11_set_136_eq : calc11_card_133.required ∪ calc11_set_134 = calc11_set_136 := by decide +kernel

theorem calc11_set_137_eq : calc11_card_133.envelope ∪ calc11_set_135 = calc11_set_137 := by decide +kernel

theorem calc11_set_138_eq : calc11_card_132.required ∪ calc11_set_136 = calc11_set_138 := by decide +kernel

theorem calc11_set_139_eq : calc11_card_132.envelope ∪ calc11_set_137 = calc11_set_139 := by decide +kernel

theorem calc11_set_140_eq : calc11_card_131.required ∪ calc11_set_138 = calc11_set_140 := by decide +kernel

theorem calc11_set_141_eq : calc11_card_131.envelope ∪ calc11_set_139 = calc11_set_141 := by decide +kernel

theorem calc11_set_142_eq : inline_802.envelope ∩ calc11_card_131.envelope = calc11_set_142 := by decide +kernel

theorem calc11_set_143_eq : calc11_card_133.envelope ∩ calc11_set_142 = calc11_set_143 := by decide +kernel

theorem calc11_set_144_eq : calc11_card_132.envelope ∩ calc11_set_143 = calc11_set_144 := by decide +kernel

theorem calc11_set_145_eq : calc11_set_140 ∪ calc11_set_144 = calc11_set_145 := by decide +kernel

theorem calc11_finishA_146 : calc11_set_145.erase (5, 6) = inline_803.required := by decide +kernel

theorem calc11_finishT_146 : insert (5, 6) calc11_set_141 = inline_803.envelope := by decide +kernel

theorem eq_inline_803 : inline_803 = combine (5, 6) [placed 2 (2, 7) card_79, placed 4 (6, 2) card_243, placed 4 (8, 1) card_518, inline_802] := by
  rw [calc11_card_131_eq, calc11_card_132_eq, calc11_card_133_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_134_eq, calc11_set_136_eq, calc11_set_138_eq, calc11_set_140_eq, calc11_set_142_eq, calc11_set_143_eq, calc11_set_144_eq, calc11_set_145_eq, calc11_finishA_146]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_135_eq, calc11_set_137_eq, calc11_set_139_eq, calc11_set_141_eq, calc11_finishT_146]
  · decide +kernel

theorem valid_inline_803 : Valid inline_803 := by
  rw [eq_inline_803]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_243
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 1) valid_518
  subst c
  exact valid_inline_802

theorem calc11_card_147_eq : placed 4 (6, 1) card_323 = calc11_card_147 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_148_eq : placed 0 (2, 1) card_430 = calc11_card_148 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_149_eq : placed 0 (1, 2) card_431 = calc11_card_149 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_150_eq : placed 7 (6, 5) card_592 = calc11_card_150 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_151_eq : placed 2 (1, 9) card_681 = calc11_card_151 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_152_eq : inline_803.required ∪ ∅ = calc11_set_152 := by decide +kernel

theorem calc11_set_153_eq : inline_803.envelope ∪ ∅ = calc11_set_153 := by decide +kernel

theorem calc11_set_154_eq : calc11_card_151.required ∪ calc11_set_152 = calc11_set_154 := by decide +kernel

theorem calc11_set_155_eq : calc11_card_151.envelope ∪ calc11_set_153 = calc11_set_155 := by decide +kernel

theorem calc11_set_156_eq : calc11_card_150.required ∪ calc11_set_154 = calc11_set_156 := by decide +kernel

theorem calc11_set_157_eq : calc11_card_150.envelope ∪ calc11_set_155 = calc11_set_157 := by decide +kernel

theorem calc11_set_158_eq : calc11_card_149.required ∪ calc11_set_156 = calc11_set_158 := by decide +kernel

theorem calc11_set_159_eq : calc11_card_149.envelope ∪ calc11_set_157 = calc11_set_159 := by decide +kernel

theorem calc11_set_160_eq : calc11_card_148.required ∪ calc11_set_158 = calc11_set_160 := by decide +kernel

theorem calc11_set_161_eq : calc11_card_148.envelope ∪ calc11_set_159 = calc11_set_161 := by decide +kernel

theorem calc11_set_162_eq : calc11_card_147.required ∪ calc11_set_160 = calc11_set_162 := by decide +kernel

theorem calc11_set_163_eq : calc11_card_147.envelope ∪ calc11_set_161 = calc11_set_163 := by decide +kernel

theorem calc11_set_164_eq : inline_803.envelope ∩ calc11_card_147.envelope = calc11_set_164 := by decide +kernel

theorem calc11_set_165_eq : calc11_card_151.envelope ∩ calc11_set_164 = calc11_set_165 := by decide +kernel

theorem calc11_set_166_eq : calc11_card_150.envelope ∩ calc11_set_165 = calc11_set_166 := by decide +kernel

theorem calc11_set_167_eq : calc11_card_149.envelope ∩ calc11_set_166 = calc11_set_167 := by decide +kernel

theorem calc11_set_168_eq : calc11_card_148.envelope ∩ calc11_set_167 = calc11_set_168 := by decide +kernel

theorem calc11_set_169_eq : calc11_set_162 ∪ calc11_set_168 = calc11_set_169 := by decide +kernel

theorem calc11_finishA_170 : calc11_set_169.erase (5, 5) = inline_804.required := by decide +kernel

theorem calc11_finishT_170 : insert (5, 5) calc11_set_163 = inline_804.envelope := by decide +kernel

theorem eq_inline_804 : inline_804 = combine (5, 5) [placed 4 (6, 1) card_323, placed 0 (2, 1) card_430, placed 0 (1, 2) card_431, placed 7 (6, 5) card_592, placed 2 (1, 9) card_681, inline_803] := by
  rw [calc11_card_147_eq, calc11_card_148_eq, calc11_card_149_eq, calc11_card_150_eq, calc11_card_151_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_152_eq, calc11_set_154_eq, calc11_set_156_eq, calc11_set_158_eq, calc11_set_160_eq, calc11_set_162_eq, calc11_set_164_eq, calc11_set_165_eq, calc11_set_166_eq, calc11_set_167_eq, calc11_set_168_eq, calc11_set_169_eq, calc11_finishA_170]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_153_eq, calc11_set_155_eq, calc11_set_157_eq, calc11_set_159_eq, calc11_set_161_eq, calc11_set_163_eq, calc11_finishT_170]
  · decide +kernel

theorem valid_inline_804 : Valid inline_804 := by
  rw [eq_inline_804]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_323
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_430
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_431
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_592
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 9) valid_681
  subst c
  exact valid_inline_803

theorem calc11_card_171_eq : placed 4 (6, 2) card_422 = calc11_card_171 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_172_eq : placed 2 (1, 8) card_450 = calc11_card_172 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_173_eq : placed 6 (6, 7) card_503 = calc11_card_173 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_174_eq : placed 0 (2, 0) card_642 = calc11_card_174 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_175_eq : placed 2 (1, 7) card_680 = calc11_card_175 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_176_eq : inline_804.required ∪ ∅ = calc11_set_176 := by decide +kernel

theorem calc11_set_177_eq : inline_804.envelope ∪ ∅ = calc11_set_177 := by decide +kernel

theorem calc11_set_178_eq : inline_801.required ∪ calc11_set_176 = calc11_set_178 := by decide +kernel

theorem calc11_set_179_eq : inline_801.envelope ∪ calc11_set_177 = calc11_set_179 := by decide +kernel

theorem calc11_set_180_eq : calc11_card_175.required ∪ calc11_set_178 = calc11_set_180 := by decide +kernel

theorem calc11_set_181_eq : calc11_card_175.envelope ∪ calc11_set_179 = calc11_set_181 := by decide +kernel

theorem calc11_set_182_eq : calc11_card_174.required ∪ calc11_set_180 = calc11_set_182 := by decide +kernel

theorem calc11_set_183_eq : calc11_card_174.envelope ∪ calc11_set_181 = calc11_set_183 := by decide +kernel

theorem calc11_set_184_eq : calc11_card_173.required ∪ calc11_set_182 = calc11_set_184 := by decide +kernel

theorem calc11_set_185_eq : calc11_card_173.envelope ∪ calc11_set_183 = calc11_set_185 := by decide +kernel

theorem calc11_set_186_eq : calc11_card_172.required ∪ calc11_set_184 = calc11_set_186 := by decide +kernel

theorem calc11_set_187_eq : calc11_card_172.envelope ∪ calc11_set_185 = calc11_set_187 := by decide +kernel

theorem calc11_set_188_eq : calc11_card_171.required ∪ calc11_set_186 = calc11_set_188 := by decide +kernel

theorem calc11_set_189_eq : calc11_card_171.envelope ∪ calc11_set_187 = calc11_set_189 := by decide +kernel

theorem calc11_set_190_eq : inline_804.envelope ∩ calc11_card_171.envelope = calc11_set_190 := by decide +kernel

theorem calc11_set_191_eq : inline_801.envelope ∩ calc11_set_190 = calc11_set_191 := by decide +kernel

theorem calc11_set_192_eq : calc11_card_175.envelope ∩ calc11_set_191 = calc11_set_192 := by decide +kernel

theorem calc11_set_193_eq : calc11_card_174.envelope ∩ calc11_set_192 = calc11_set_193 := by decide +kernel

theorem calc11_set_194_eq : calc11_card_173.envelope ∩ calc11_set_193 = calc11_set_194 := by decide +kernel

theorem calc11_set_195_eq : calc11_card_172.envelope ∩ calc11_set_194 = calc11_set_195 := by decide +kernel

theorem calc11_set_196_eq : calc11_set_188 ∪ calc11_set_195 = calc11_set_196 := by decide +kernel

theorem calc11_finishA_197 : calc11_set_196.erase (5, 4) = card_705.required := by decide +kernel

theorem calc11_finishT_197 : insert (5, 4) calc11_set_189 = card_705.envelope := by decide +kernel

theorem eq_card_705 : card_705 = combine (5, 4) [placed 4 (6, 2) card_422, placed 2 (1, 8) card_450, placed 6 (6, 7) card_503, placed 0 (2, 0) card_642, placed 2 (1, 7) card_680, inline_801, inline_804] := by
  rw [calc11_card_171_eq, calc11_card_172_eq, calc11_card_173_eq, calc11_card_174_eq, calc11_card_175_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_176_eq, calc11_set_178_eq, calc11_set_180_eq, calc11_set_182_eq, calc11_set_184_eq, calc11_set_186_eq, calc11_set_188_eq, calc11_set_190_eq, calc11_set_191_eq, calc11_set_192_eq, calc11_set_193_eq, calc11_set_194_eq, calc11_set_195_eq, calc11_set_196_eq, calc11_finishA_197]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_177_eq, calc11_set_179_eq, calc11_set_181_eq, calc11_set_183_eq, calc11_set_185_eq, calc11_set_187_eq, calc11_set_189_eq, calc11_finishT_197]
  · decide +kernel

theorem valid_705 : Valid card_705 := by
  rw [eq_card_705]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 2) valid_422
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_450
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 7) valid_503
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_642
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_680
  rcases hc with rfl | hc
  · exact valid_inline_801
  subst c
  exact valid_inline_804

theorem calc11_card_198_eq : placed 2 (3, 4) card_4 = calc11_card_198 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_199_eq : placed 1 (2, 3) card_9 = calc11_card_199 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_200_eq : calc11_card_199.required ∪ ∅ = calc11_set_200 := by decide +kernel

theorem calc11_set_201_eq : calc11_card_199.envelope ∪ ∅ = calc11_set_201 := by decide +kernel

theorem calc11_set_202_eq : calc11_card_198.required ∪ calc11_set_200 = calc11_set_202 := by decide +kernel

theorem calc11_set_203_eq : calc11_card_198.envelope ∪ calc11_set_201 = calc11_set_203 := by decide +kernel

theorem calc11_set_204_eq : calc11_card_199.envelope ∩ calc11_card_198.envelope = calc11_set_204 := by decide +kernel

theorem calc11_set_205_eq : calc11_set_202 ∪ calc11_set_204 = calc11_set_205 := by decide +kernel

theorem calc11_finishA_206 : calc11_set_205.erase (6, 4) = inline_805.required := by decide +kernel

theorem calc11_finishT_206 : insert (6, 4) calc11_set_203 = inline_805.envelope := by decide +kernel

theorem eq_inline_805 : inline_805 = combine (6, 4) [placed 2 (3, 4) card_4, placed 1 (2, 3) card_9] := by
  rw [calc11_card_198_eq, calc11_card_199_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_200_eq, calc11_set_202_eq, calc11_set_204_eq, calc11_set_205_eq, calc11_finishA_206]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_201_eq, calc11_set_203_eq, calc11_finishT_206]
  · decide +kernel

theorem valid_inline_805 : Valid inline_805 := by
  rw [eq_inline_805]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 4) valid_4
  subst c
  exact placed_valid 1 (2, 3) valid_9

theorem calc11_card_207_eq : placed 5 (3, 4) card_154 = calc11_card_207 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_208_eq : placed 2 (3, 6) card_159 = calc11_card_208 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_209_eq : calc11_card_208.required ∪ ∅ = calc11_set_209 := by decide +kernel

theorem calc11_set_210_eq : calc11_card_208.envelope ∪ ∅ = calc11_set_210 := by decide +kernel

theorem calc11_set_211_eq : calc11_card_207.required ∪ calc11_set_209 = calc11_set_211 := by decide +kernel

theorem calc11_set_212_eq : calc11_card_207.envelope ∪ calc11_set_210 = calc11_set_212 := by decide +kernel

theorem calc11_set_213_eq : calc11_card_208.envelope ∩ calc11_card_207.envelope = calc11_set_213 := by decide +kernel

theorem calc11_set_214_eq : calc11_set_211 ∪ calc11_set_213 = calc11_set_214 := by decide +kernel

theorem calc11_finishA_215 : calc11_set_214.erase (5, 3) = inline_806.required := by decide +kernel

theorem calc11_finishT_215 : insert (5, 3) calc11_set_212 = inline_806.envelope := by decide +kernel

theorem eq_inline_806 : inline_806 = combine (5, 3) [placed 5 (3, 4) card_154, placed 2 (3, 6) card_159] := by
  rw [calc11_card_207_eq, calc11_card_208_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_209_eq, calc11_set_211_eq, calc11_set_213_eq, calc11_set_214_eq, calc11_finishA_215]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_210_eq, calc11_set_212_eq, calc11_finishT_215]
  · decide +kernel

theorem valid_inline_806 : Valid inline_806 := by
  rw [eq_inline_806]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_154
  subst c
  exact placed_valid 2 (3, 6) valid_159

theorem calc11_card_216_eq : placed 5 (3, 5) card_22 = calc11_card_216 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_217_eq : placed 4 (8, 2) card_152 = calc11_card_217 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_218_eq : placed 0 (4, 1) card_166 = calc11_card_218 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_219_eq : calc11_card_218.required ∪ ∅ = calc11_set_219 := by decide +kernel

theorem calc11_set_220_eq : calc11_card_218.envelope ∪ ∅ = calc11_set_220 := by decide +kernel

theorem calc11_set_221_eq : calc11_card_217.required ∪ calc11_set_219 = calc11_set_221 := by decide +kernel

theorem calc11_set_222_eq : calc11_card_217.envelope ∪ calc11_set_220 = calc11_set_222 := by decide +kernel

theorem calc11_set_223_eq : calc11_card_216.required ∪ calc11_set_221 = calc11_set_223 := by decide +kernel

theorem calc11_set_224_eq : calc11_card_216.envelope ∪ calc11_set_222 = calc11_set_224 := by decide +kernel

theorem calc11_set_225_eq : calc11_card_218.envelope ∩ calc11_card_216.envelope = calc11_set_225 := by decide +kernel

theorem calc11_set_226_eq : calc11_card_217.envelope ∩ calc11_set_225 = calc11_set_226 := by decide +kernel

theorem calc11_set_227_eq : calc11_set_223 ∪ calc11_set_226 = calc11_set_227 := by decide +kernel

theorem calc11_finishA_228 : calc11_set_227.erase (7, 5) = inline_807.required := by decide +kernel

theorem calc11_finishT_228 : insert (7, 5) calc11_set_224 = inline_807.envelope := by decide +kernel

theorem eq_inline_807 : inline_807 = combine (7, 5) [placed 5 (3, 5) card_22, placed 4 (8, 2) card_152, placed 0 (4, 1) card_166] := by
  rw [calc11_card_216_eq, calc11_card_217_eq, calc11_card_218_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_219_eq, calc11_set_221_eq, calc11_set_223_eq, calc11_set_225_eq, calc11_set_226_eq, calc11_set_227_eq, calc11_finishA_228]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_220_eq, calc11_set_222_eq, calc11_set_224_eq, calc11_finishT_228]
  · decide +kernel

theorem valid_inline_807 : Valid inline_807 := by
  rw [eq_inline_807]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 2) valid_152
  subst c
  exact placed_valid 0 (4, 1) valid_166

theorem calc11_card_229_eq : placed 5 (3, 4) card_261 = calc11_card_229 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_230_eq : inline_807.required ∪ ∅ = calc11_set_230 := by decide +kernel

theorem calc11_set_231_eq : inline_807.envelope ∪ ∅ = calc11_set_231 := by decide +kernel

theorem calc11_set_232_eq : inline_806.required ∪ calc11_set_230 = calc11_set_232 := by decide +kernel

theorem calc11_set_233_eq : inline_806.envelope ∪ calc11_set_231 = calc11_set_233 := by decide +kernel

theorem calc11_set_234_eq : inline_805.required ∪ calc11_set_232 = calc11_set_234 := by decide +kernel

theorem calc11_set_235_eq : inline_805.envelope ∪ calc11_set_233 = calc11_set_235 := by decide +kernel

theorem calc11_set_236_eq : calc11_card_229.required ∪ calc11_set_234 = calc11_set_236 := by decide +kernel

theorem calc11_set_237_eq : calc11_card_229.envelope ∪ calc11_set_235 = calc11_set_237 := by decide +kernel

theorem calc11_set_238_eq : inline_807.envelope ∩ calc11_card_229.envelope = calc11_set_238 := by decide +kernel

theorem calc11_set_239_eq : inline_806.envelope ∩ calc11_set_238 = calc11_set_239 := by decide +kernel

theorem calc11_set_240_eq : inline_805.envelope ∩ calc11_set_239 = calc11_set_240 := by decide +kernel

theorem calc11_set_241_eq : calc11_set_236 ∪ calc11_set_240 = calc11_set_241 := by decide +kernel

theorem calc11_finishA_242 : calc11_set_241.erase (7, 3) = inline_808.required := by decide +kernel

theorem calc11_finishT_242 : insert (7, 3) calc11_set_237 = inline_808.envelope := by decide +kernel

theorem eq_inline_808 : inline_808 = combine (7, 3) [placed 5 (3, 4) card_261, inline_805, inline_806, inline_807] := by
  rw [calc11_card_229_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_230_eq, calc11_set_232_eq, calc11_set_234_eq, calc11_set_236_eq, calc11_set_238_eq, calc11_set_239_eq, calc11_set_240_eq, calc11_set_241_eq, calc11_finishA_242]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_231_eq, calc11_set_233_eq, calc11_set_235_eq, calc11_set_237_eq, calc11_finishT_242]
  · decide +kernel

theorem valid_inline_808 : Valid inline_808 := by
  rw [eq_inline_808]
  apply combination_rule (7, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_261
  rcases hc with rfl | hc
  · exact valid_inline_805
  rcases hc with rfl | hc
  · exact valid_inline_806
  subst c
  exact valid_inline_807

theorem calc11_card_243_eq : placed 1 (2, 4) card_15 = calc11_card_243 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_244_eq : placed 5 (1, 5) card_65 = calc11_card_244 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_245_eq : inline_808.required ∪ ∅ = calc11_set_245 := by decide +kernel

theorem calc11_set_246_eq : inline_808.envelope ∪ ∅ = calc11_set_246 := by decide +kernel

theorem calc11_set_247_eq : calc11_card_244.required ∪ calc11_set_245 = calc11_set_247 := by decide +kernel

theorem calc11_set_248_eq : calc11_card_244.envelope ∪ calc11_set_246 = calc11_set_248 := by decide +kernel

theorem calc11_set_249_eq : calc11_card_243.required ∪ calc11_set_247 = calc11_set_249 := by decide +kernel

theorem calc11_set_250_eq : calc11_card_243.envelope ∪ calc11_set_248 = calc11_set_250 := by decide +kernel

theorem calc11_set_251_eq : inline_808.envelope ∩ calc11_card_243.envelope = calc11_set_251 := by decide +kernel

theorem calc11_set_252_eq : calc11_card_244.envelope ∩ calc11_set_251 = calc11_set_252 := by decide +kernel

theorem calc11_set_253_eq : calc11_set_249 ∪ calc11_set_252 = calc11_set_253 := by decide +kernel

theorem calc11_finishA_254 : calc11_set_253.erase (3, 4) = inline_809.required := by decide +kernel

theorem calc11_finishT_254 : insert (3, 4) calc11_set_250 = inline_809.envelope := by decide +kernel

theorem eq_inline_809 : inline_809 = combine (3, 4) [placed 1 (2, 4) card_15, placed 5 (1, 5) card_65, inline_808] := by
  rw [calc11_card_243_eq, calc11_card_244_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_245_eq, calc11_set_247_eq, calc11_set_249_eq, calc11_set_251_eq, calc11_set_252_eq, calc11_set_253_eq, calc11_finishA_254]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_246_eq, calc11_set_248_eq, calc11_set_250_eq, calc11_finishT_254]
  · decide +kernel

theorem valid_inline_809 : Valid inline_809 := by
  rw [eq_inline_809]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_65
  subst c
  exact valid_inline_808

theorem calc11_card_255_eq : placed 1 (0, 3) card_318 = calc11_card_255 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_256_eq : placed 7 (7, 4) card_334 = calc11_card_256 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_257_eq : placed 5 (3, 5) card_379 = calc11_card_257 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_258_eq : calc11_card_257.required ∪ ∅ = calc11_set_258 := by decide +kernel

theorem calc11_set_259_eq : calc11_card_257.envelope ∪ ∅ = calc11_set_259 := by decide +kernel

theorem calc11_set_260_eq : calc11_card_256.required ∪ calc11_set_258 = calc11_set_260 := by decide +kernel

theorem calc11_set_261_eq : calc11_card_256.envelope ∪ calc11_set_259 = calc11_set_261 := by decide +kernel

theorem calc11_set_262_eq : calc11_card_255.required ∪ calc11_set_260 = calc11_set_262 := by decide +kernel

theorem calc11_set_263_eq : calc11_card_255.envelope ∪ calc11_set_261 = calc11_set_263 := by decide +kernel

theorem calc11_set_264_eq : calc11_card_257.envelope ∩ calc11_card_255.envelope = calc11_set_264 := by decide +kernel

theorem calc11_set_265_eq : calc11_card_256.envelope ∩ calc11_set_264 = calc11_set_265 := by decide +kernel

theorem calc11_set_266_eq : calc11_set_262 ∪ calc11_set_265 = calc11_set_266 := by decide +kernel

theorem calc11_finishA_267 : calc11_set_266.erase (3, 3) = inline_810.required := by decide +kernel

theorem calc11_finishT_267 : insert (3, 3) calc11_set_263 = inline_810.envelope := by decide +kernel

theorem eq_inline_810 : inline_810 = combine (3, 3) [placed 1 (0, 3) card_318, placed 7 (7, 4) card_334, placed 5 (3, 5) card_379] := by
  rw [calc11_card_255_eq, calc11_card_256_eq, calc11_card_257_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_258_eq, calc11_set_260_eq, calc11_set_262_eq, calc11_set_264_eq, calc11_set_265_eq, calc11_set_266_eq, calc11_finishA_267]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_259_eq, calc11_set_261_eq, calc11_set_263_eq, calc11_finishT_267]
  · decide +kernel

theorem valid_inline_810 : Valid inline_810 := by
  rw [eq_inline_810]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_318
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 4) valid_334
  subst c
  exact placed_valid 5 (3, 5) valid_379

theorem calc11_card_268_eq : placed 7 (6, 5) card_66 = calc11_card_268 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_269_eq : placed 7 (6, 6) card_238 = calc11_card_269 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_270_eq : placed 5 (2, 5) card_394 = calc11_card_270 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_271_eq : calc11_card_270.required ∪ ∅ = calc11_set_271 := by decide +kernel

theorem calc11_set_272_eq : calc11_card_270.envelope ∪ ∅ = calc11_set_272 := by decide +kernel

theorem calc11_set_273_eq : calc11_card_269.required ∪ calc11_set_271 = calc11_set_273 := by decide +kernel

theorem calc11_set_274_eq : calc11_card_269.envelope ∪ calc11_set_272 = calc11_set_274 := by decide +kernel

theorem calc11_set_275_eq : calc11_card_268.required ∪ calc11_set_273 = calc11_set_275 := by decide +kernel

theorem calc11_set_276_eq : calc11_card_268.envelope ∪ calc11_set_274 = calc11_set_276 := by decide +kernel

theorem calc11_set_277_eq : calc11_card_270.envelope ∩ calc11_card_268.envelope = calc11_set_277 := by decide +kernel

theorem calc11_set_278_eq : calc11_card_269.envelope ∩ calc11_set_277 = calc11_set_278 := by decide +kernel

theorem calc11_set_279_eq : calc11_set_275 ∪ calc11_set_278 = calc11_set_279 := by decide +kernel

theorem calc11_finishA_280 : calc11_set_279.erase (3, 4) = inline_811.required := by decide +kernel

theorem calc11_finishT_280 : insert (3, 4) calc11_set_276 = inline_811.envelope := by decide +kernel

theorem eq_inline_811 : inline_811 = combine (3, 4) [placed 7 (6, 5) card_66, placed 7 (6, 6) card_238, placed 5 (2, 5) card_394] := by
  rw [calc11_card_268_eq, calc11_card_269_eq, calc11_card_270_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_271_eq, calc11_set_273_eq, calc11_set_275_eq, calc11_set_277_eq, calc11_set_278_eq, calc11_set_279_eq, calc11_finishA_280]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_272_eq, calc11_set_274_eq, calc11_set_276_eq, calc11_finishT_280]
  · decide +kernel

theorem valid_inline_811 : Valid inline_811 := by
  rw [eq_inline_811]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_66
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_238
  subst c
  exact placed_valid 5 (2, 5) valid_394

theorem calc11_card_281_eq : placed 7 (7, 5) card_417 = calc11_card_281 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_282_eq : placed 7 (6, 5) card_420 = calc11_card_282 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_283_eq : placed 7 (6, 5) card_526 = calc11_card_283 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_284_eq : placed 5 (0, 6) card_532 = calc11_card_284 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_285_eq : inline_811.required ∪ ∅ = calc11_set_285 := by decide +kernel

theorem calc11_set_286_eq : inline_811.envelope ∪ ∅ = calc11_set_286 := by decide +kernel

theorem calc11_set_287_eq : inline_810.required ∪ calc11_set_285 = calc11_set_287 := by decide +kernel

theorem calc11_set_288_eq : inline_810.envelope ∪ calc11_set_286 = calc11_set_288 := by decide +kernel

theorem calc11_set_289_eq : calc11_card_284.required ∪ calc11_set_287 = calc11_set_289 := by decide +kernel

theorem calc11_set_290_eq : calc11_card_284.envelope ∪ calc11_set_288 = calc11_set_290 := by decide +kernel

theorem calc11_set_291_eq : calc11_card_283.required ∪ calc11_set_289 = calc11_set_291 := by decide +kernel

theorem calc11_set_292_eq : calc11_card_283.envelope ∪ calc11_set_290 = calc11_set_292 := by decide +kernel

theorem calc11_set_293_eq : calc11_card_282.required ∪ calc11_set_291 = calc11_set_293 := by decide +kernel

theorem calc11_set_294_eq : calc11_card_282.envelope ∪ calc11_set_292 = calc11_set_294 := by decide +kernel

theorem calc11_set_295_eq : calc11_card_281.required ∪ calc11_set_293 = calc11_set_295 := by decide +kernel

theorem calc11_set_296_eq : calc11_card_281.envelope ∪ calc11_set_294 = calc11_set_296 := by decide +kernel

theorem calc11_set_297_eq : inline_811.envelope ∩ calc11_card_281.envelope = calc11_set_297 := by decide +kernel

theorem calc11_set_298_eq : inline_810.envelope ∩ calc11_set_297 = calc11_set_298 := by decide +kernel

theorem calc11_set_299_eq : calc11_card_284.envelope ∩ calc11_set_298 = calc11_set_299 := by decide +kernel

theorem calc11_set_300_eq : calc11_card_283.envelope ∩ calc11_set_299 = calc11_set_300 := by decide +kernel

theorem calc11_set_301_eq : calc11_card_282.envelope ∩ calc11_set_300 = calc11_set_301 := by decide +kernel

theorem calc11_set_302_eq : calc11_set_295 ∪ calc11_set_301 = calc11_set_302 := by decide +kernel

theorem calc11_finishA_303 : calc11_set_302.erase (5, 3) = inline_812.required := by decide +kernel

theorem calc11_finishT_303 : insert (5, 3) calc11_set_296 = inline_812.envelope := by decide +kernel

theorem eq_inline_812 : inline_812 = combine (5, 3) [placed 7 (7, 5) card_417, placed 7 (6, 5) card_420, placed 7 (6, 5) card_526, placed 5 (0, 6) card_532, inline_810, inline_811] := by
  rw [calc11_card_281_eq, calc11_card_282_eq, calc11_card_283_eq, calc11_card_284_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_285_eq, calc11_set_287_eq, calc11_set_289_eq, calc11_set_291_eq, calc11_set_293_eq, calc11_set_295_eq, calc11_set_297_eq, calc11_set_298_eq, calc11_set_299_eq, calc11_set_300_eq, calc11_set_301_eq, calc11_set_302_eq, calc11_finishA_303]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_286_eq, calc11_set_288_eq, calc11_set_290_eq, calc11_set_292_eq, calc11_set_294_eq, calc11_set_296_eq, calc11_finishT_303]
  · decide +kernel

theorem valid_inline_812 : Valid inline_812 := by
  rw [eq_inline_812]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 5) valid_417
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_420
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_526
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_532
  rcases hc with rfl | hc
  · exact valid_inline_810
  subst c
  exact valid_inline_811

theorem calc11_card_304_eq : placed 1 (4, 4) card_30 = calc11_card_304 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_305_eq : placed 0 (4, 1) card_59 = calc11_card_305 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_306_eq : placed 5 (3, 6) card_296 = calc11_card_306 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_307_eq : placed 0 (6, 1) card_603 = calc11_card_307 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_308_eq : calc11_card_307.required ∪ ∅ = calc11_set_308 := by decide +kernel

theorem calc11_set_309_eq : calc11_card_307.envelope ∪ ∅ = calc11_set_309 := by decide +kernel

theorem calc11_set_310_eq : calc11_card_306.required ∪ calc11_set_308 = calc11_set_310 := by decide +kernel

theorem calc11_set_311_eq : calc11_card_306.envelope ∪ calc11_set_309 = calc11_set_311 := by decide +kernel

theorem calc11_set_312_eq : calc11_card_305.required ∪ calc11_set_310 = calc11_set_312 := by decide +kernel

theorem calc11_set_313_eq : calc11_card_305.envelope ∪ calc11_set_311 = calc11_set_313 := by decide +kernel

theorem calc11_set_314_eq : calc11_card_304.required ∪ calc11_set_312 = calc11_set_314 := by decide +kernel

theorem calc11_set_315_eq : calc11_card_304.envelope ∪ calc11_set_313 = calc11_set_315 := by decide +kernel

theorem calc11_set_316_eq : calc11_card_307.envelope ∩ calc11_card_304.envelope = calc11_set_316 := by decide +kernel

theorem calc11_set_317_eq : calc11_card_306.envelope ∩ calc11_set_316 = calc11_set_317 := by decide +kernel

theorem calc11_set_318_eq : calc11_card_305.envelope ∩ calc11_set_317 = calc11_set_318 := by decide +kernel

theorem calc11_set_319_eq : calc11_set_314 ∪ calc11_set_318 = calc11_set_319 := by decide +kernel

theorem calc11_finishA_320 : calc11_set_319.erase (7, 4) = inline_813.required := by decide +kernel

theorem calc11_finishT_320 : insert (7, 4) calc11_set_315 = inline_813.envelope := by decide +kernel

theorem eq_inline_813 : inline_813 = combine (7, 4) [placed 1 (4, 4) card_30, placed 0 (4, 1) card_59, placed 5 (3, 6) card_296, placed 0 (6, 1) card_603] := by
  rw [calc11_card_304_eq, calc11_card_305_eq, calc11_card_306_eq, calc11_card_307_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_308_eq, calc11_set_310_eq, calc11_set_312_eq, calc11_set_314_eq, calc11_set_316_eq, calc11_set_317_eq, calc11_set_318_eq, calc11_set_319_eq, calc11_finishA_320]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_309_eq, calc11_set_311_eq, calc11_set_313_eq, calc11_set_315_eq, calc11_finishT_320]
  · decide +kernel

theorem valid_inline_813 : Valid inline_813 := by
  rw [eq_inline_813]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_30
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_296
  subst c
  exact placed_valid 0 (6, 1) valid_603

theorem calc11_card_321_eq : placed 5 (3, 5) card_22 = calc11_card_321 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_322_eq : placed 5 (4, 5) card_74 = calc11_card_322 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_323_eq : placed 2 (3, 9) card_325 = calc11_card_323 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_324_eq : inline_813.required ∪ ∅ = calc11_set_324 := by decide +kernel

theorem calc11_set_325_eq : inline_813.envelope ∪ ∅ = calc11_set_325 := by decide +kernel

theorem calc11_set_326_eq : calc11_card_323.required ∪ calc11_set_324 = calc11_set_326 := by decide +kernel

theorem calc11_set_327_eq : calc11_card_323.envelope ∪ calc11_set_325 = calc11_set_327 := by decide +kernel

theorem calc11_set_328_eq : calc11_card_322.required ∪ calc11_set_326 = calc11_set_328 := by decide +kernel

theorem calc11_set_329_eq : calc11_card_322.envelope ∪ calc11_set_327 = calc11_set_329 := by decide +kernel

theorem calc11_set_330_eq : calc11_card_321.required ∪ calc11_set_328 = calc11_set_330 := by decide +kernel

theorem calc11_set_331_eq : calc11_card_321.envelope ∪ calc11_set_329 = calc11_set_331 := by decide +kernel

theorem calc11_set_332_eq : inline_813.envelope ∩ calc11_card_321.envelope = calc11_set_332 := by decide +kernel

theorem calc11_set_333_eq : calc11_card_323.envelope ∩ calc11_set_332 = calc11_set_333 := by decide +kernel

theorem calc11_set_334_eq : calc11_card_322.envelope ∩ calc11_set_333 = calc11_set_334 := by decide +kernel

theorem calc11_set_335_eq : calc11_set_330 ∪ calc11_set_334 = calc11_set_335 := by decide +kernel

theorem calc11_finishA_336 : calc11_set_335.erase (7, 5) = inline_814.required := by decide +kernel

theorem calc11_finishT_336 : insert (7, 5) calc11_set_331 = inline_814.envelope := by decide +kernel

theorem eq_inline_814 : inline_814 = combine (7, 5) [placed 5 (3, 5) card_22, placed 5 (4, 5) card_74, placed 2 (3, 9) card_325, inline_813] := by
  rw [calc11_card_321_eq, calc11_card_322_eq, calc11_card_323_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_324_eq, calc11_set_326_eq, calc11_set_328_eq, calc11_set_330_eq, calc11_set_332_eq, calc11_set_333_eq, calc11_set_334_eq, calc11_set_335_eq, calc11_finishA_336]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_325_eq, calc11_set_327_eq, calc11_set_329_eq, calc11_set_331_eq, calc11_finishT_336]
  · decide +kernel

theorem valid_inline_814 : Valid inline_814 := by
  rw [eq_inline_814]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 5) valid_74
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_325
  subst c
  exact valid_inline_813

theorem calc11_card_337_eq : placed 7 (8, 6) card_512 = calc11_card_337 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_338_eq : placed 5 (1, 6) card_517 = calc11_card_338 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_339_eq : placed 7 (8, 6) card_527 = calc11_card_339 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_340_eq : placed 7 (8, 6) card_537 = calc11_card_340 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_341_eq : inline_814.required ∪ ∅ = calc11_set_341 := by decide +kernel

theorem calc11_set_342_eq : inline_814.envelope ∪ ∅ = calc11_set_342 := by decide +kernel

theorem calc11_set_343_eq : inline_812.required ∪ calc11_set_341 = calc11_set_343 := by decide +kernel

theorem calc11_set_344_eq : inline_812.envelope ∪ calc11_set_342 = calc11_set_344 := by decide +kernel

theorem calc11_set_345_eq : inline_809.required ∪ calc11_set_343 = calc11_set_345 := by decide +kernel

theorem calc11_set_346_eq : inline_809.envelope ∪ calc11_set_344 = calc11_set_346 := by decide +kernel

theorem calc11_set_347_eq : calc11_card_340.required ∪ calc11_set_345 = calc11_set_347 := by decide +kernel

theorem calc11_set_348_eq : calc11_card_340.envelope ∪ calc11_set_346 = calc11_set_348 := by decide +kernel

theorem calc11_set_349_eq : calc11_card_339.required ∪ calc11_set_347 = calc11_set_349 := by decide +kernel

theorem calc11_set_350_eq : calc11_card_339.envelope ∪ calc11_set_348 = calc11_set_350 := by decide +kernel

theorem calc11_set_351_eq : calc11_card_338.required ∪ calc11_set_349 = calc11_set_351 := by decide +kernel

theorem calc11_set_352_eq : calc11_card_338.envelope ∪ calc11_set_350 = calc11_set_352 := by decide +kernel

theorem calc11_set_353_eq : calc11_card_337.required ∪ calc11_set_351 = calc11_set_353 := by decide +kernel

theorem calc11_set_354_eq : calc11_card_337.envelope ∪ calc11_set_352 = calc11_set_354 := by decide +kernel

theorem calc11_set_355_eq : inline_814.envelope ∩ calc11_card_337.envelope = calc11_set_355 := by decide +kernel

theorem calc11_set_356_eq : inline_812.envelope ∩ calc11_set_355 = calc11_set_356 := by decide +kernel

theorem calc11_set_357_eq : inline_809.envelope ∩ calc11_set_356 = calc11_set_357 := by decide +kernel

theorem calc11_set_358_eq : calc11_card_340.envelope ∩ calc11_set_357 = calc11_set_358 := by decide +kernel

theorem calc11_set_359_eq : calc11_card_339.envelope ∩ calc11_set_358 = calc11_set_359 := by decide +kernel

theorem calc11_set_360_eq : calc11_card_338.envelope ∩ calc11_set_359 = calc11_set_360 := by decide +kernel

theorem calc11_set_361_eq : calc11_set_353 ∪ calc11_set_360 = calc11_set_361 := by decide +kernel

theorem calc11_finishA_362 : calc11_set_361.erase (4, 4) = card_706.required := by decide +kernel

theorem calc11_finishT_362 : insert (4, 4) calc11_set_354 = card_706.envelope := by decide +kernel

theorem eq_card_706 : card_706 = combine (4, 4) [placed 7 (8, 6) card_512, placed 5 (1, 6) card_517, placed 7 (8, 6) card_527, placed 7 (8, 6) card_537, inline_809, inline_812, inline_814] := by
  rw [calc11_card_337_eq, calc11_card_338_eq, calc11_card_339_eq, calc11_card_340_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_341_eq, calc11_set_343_eq, calc11_set_345_eq, calc11_set_347_eq, calc11_set_349_eq, calc11_set_351_eq, calc11_set_353_eq, calc11_set_355_eq, calc11_set_356_eq, calc11_set_357_eq, calc11_set_358_eq, calc11_set_359_eq, calc11_set_360_eq, calc11_set_361_eq, calc11_finishA_362]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_342_eq, calc11_set_344_eq, calc11_set_346_eq, calc11_set_348_eq, calc11_set_350_eq, calc11_set_352_eq, calc11_set_354_eq, calc11_finishT_362]
  · decide +kernel

theorem valid_706 : Valid card_706 := by
  rw [eq_card_706]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_512
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_517
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_527
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_537
  rcases hc with rfl | hc
  · exact valid_inline_809
  rcases hc with rfl | hc
  · exact valid_inline_812
  subst c
  exact valid_inline_814

theorem calc11_card_363_eq : placed 5 (2, 8) card_116 = calc11_card_363 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_364_eq : placed 3 (7, 4) card_134 = calc11_card_364 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_365_eq : placed 3 (7, 4) card_180 = calc11_card_365 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_366_eq : placed 0 (4, 2) card_337 = calc11_card_366 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_367_eq : placed 3 (8, 4) card_435 = calc11_card_367 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_368_eq : placed 3 (7, 5) card_558 = calc11_card_368 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_369_eq : placed 1 (0, 3) card_662 = calc11_card_369 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_370_eq : calc11_card_369.required ∪ ∅ = calc11_set_370 := by decide +kernel

theorem calc11_set_371_eq : calc11_card_369.envelope ∪ ∅ = calc11_set_371 := by decide +kernel

theorem calc11_set_372_eq : calc11_card_368.required ∪ calc11_set_370 = calc11_set_372 := by decide +kernel

theorem calc11_set_373_eq : calc11_card_368.envelope ∪ calc11_set_371 = calc11_set_373 := by decide +kernel

theorem calc11_set_374_eq : calc11_card_367.required ∪ calc11_set_372 = calc11_set_374 := by decide +kernel

theorem calc11_set_375_eq : calc11_card_367.envelope ∪ calc11_set_373 = calc11_set_375 := by decide +kernel

theorem calc11_set_376_eq : calc11_card_366.required ∪ calc11_set_374 = calc11_set_376 := by decide +kernel

theorem calc11_set_377_eq : calc11_card_366.envelope ∪ calc11_set_375 = calc11_set_377 := by decide +kernel

theorem calc11_set_378_eq : calc11_card_365.required ∪ calc11_set_376 = calc11_set_378 := by decide +kernel

theorem calc11_set_379_eq : calc11_card_365.envelope ∪ calc11_set_377 = calc11_set_379 := by decide +kernel

theorem calc11_set_380_eq : calc11_card_364.required ∪ calc11_set_378 = calc11_set_380 := by decide +kernel

theorem calc11_set_381_eq : calc11_card_364.envelope ∪ calc11_set_379 = calc11_set_381 := by decide +kernel

theorem calc11_set_382_eq : calc11_card_363.required ∪ calc11_set_380 = calc11_set_382 := by decide +kernel

theorem calc11_set_383_eq : calc11_card_363.envelope ∪ calc11_set_381 = calc11_set_383 := by decide +kernel

theorem calc11_set_384_eq : calc11_card_369.envelope ∩ calc11_card_363.envelope = calc11_set_384 := by decide +kernel

theorem calc11_set_385_eq : calc11_card_368.envelope ∩ calc11_set_384 = calc11_set_385 := by decide +kernel

theorem calc11_set_386_eq : calc11_card_367.envelope ∩ calc11_set_385 = calc11_set_386 := by decide +kernel

theorem calc11_set_387_eq : calc11_card_366.envelope ∩ calc11_set_386 = calc11_set_387 := by decide +kernel

theorem calc11_set_388_eq : calc11_card_365.envelope ∩ calc11_set_387 = calc11_set_388 := by decide +kernel

theorem calc11_set_389_eq : calc11_card_364.envelope ∩ calc11_set_388 = calc11_set_389 := by decide +kernel

theorem calc11_set_390_eq : calc11_set_382 ∪ calc11_set_389 = calc11_set_390 := by decide +kernel

theorem calc11_finishA_391 : calc11_set_390.erase (5, 7) = inline_815.required := by decide +kernel

theorem calc11_finishT_391 : insert (5, 7) calc11_set_383 = inline_815.envelope := by decide +kernel

theorem eq_inline_815 : inline_815 = combine (5, 7) [placed 5 (2, 8) card_116, placed 3 (7, 4) card_134, placed 3 (7, 4) card_180, placed 0 (4, 2) card_337, placed 3 (8, 4) card_435, placed 3 (7, 5) card_558, placed 1 (0, 3) card_662] := by
  rw [calc11_card_363_eq, calc11_card_364_eq, calc11_card_365_eq, calc11_card_366_eq, calc11_card_367_eq, calc11_card_368_eq, calc11_card_369_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_370_eq, calc11_set_372_eq, calc11_set_374_eq, calc11_set_376_eq, calc11_set_378_eq, calc11_set_380_eq, calc11_set_382_eq, calc11_set_384_eq, calc11_set_385_eq, calc11_set_386_eq, calc11_set_387_eq, calc11_set_388_eq, calc11_set_389_eq, calc11_set_390_eq, calc11_finishA_391]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_371_eq, calc11_set_373_eq, calc11_set_375_eq, calc11_set_377_eq, calc11_set_379_eq, calc11_set_381_eq, calc11_set_383_eq, calc11_finishT_391]
  · decide +kernel

theorem valid_inline_815 : Valid inline_815 := by
  rw [eq_inline_815]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_337
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 5) valid_558
  subst c
  exact placed_valid 1 (0, 3) valid_662

theorem calc11_card_392_eq : placed 0 (5, 3) card_7 = calc11_card_392 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_393_eq : placed 4 (6, 3) card_9 = calc11_card_393 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_394_eq : placed 3 (6, 4) card_380 = calc11_card_394 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_395_eq : calc11_card_394.required ∪ ∅ = calc11_set_395 := by decide +kernel

theorem calc11_set_396_eq : calc11_card_394.envelope ∪ ∅ = calc11_set_396 := by decide +kernel

theorem calc11_set_397_eq : calc11_card_393.required ∪ calc11_set_395 = calc11_set_397 := by decide +kernel

theorem calc11_set_398_eq : calc11_card_393.envelope ∪ calc11_set_396 = calc11_set_398 := by decide +kernel

theorem calc11_set_399_eq : calc11_card_392.required ∪ calc11_set_397 = calc11_set_399 := by decide +kernel

theorem calc11_set_400_eq : calc11_card_392.envelope ∪ calc11_set_398 = calc11_set_400 := by decide +kernel

theorem calc11_set_401_eq : calc11_card_394.envelope ∩ calc11_card_392.envelope = calc11_set_401 := by decide +kernel

theorem calc11_set_402_eq : calc11_card_393.envelope ∩ calc11_set_401 = calc11_set_402 := by decide +kernel

theorem calc11_set_403_eq : calc11_set_399 ∪ calc11_set_402 = calc11_set_403 := by decide +kernel

theorem calc11_finishA_404 : calc11_set_403.erase (5, 7) = inline_816.required := by decide +kernel

theorem calc11_finishT_404 : insert (5, 7) calc11_set_400 = inline_816.envelope := by decide +kernel

theorem eq_inline_816 : inline_816 = combine (5, 7) [placed 0 (5, 3) card_7, placed 4 (6, 3) card_9, placed 3 (6, 4) card_380] := by
  rw [calc11_card_392_eq, calc11_card_393_eq, calc11_card_394_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_395_eq, calc11_set_397_eq, calc11_set_399_eq, calc11_set_401_eq, calc11_set_402_eq, calc11_set_403_eq, calc11_finishA_404]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_396_eq, calc11_set_398_eq, calc11_set_400_eq, calc11_finishT_404]
  · decide +kernel

theorem valid_inline_816 : Valid inline_816 := by
  rw [eq_inline_816]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_9
  subst c
  exact placed_valid 3 (6, 4) valid_380

theorem calc11_card_405_eq : placed 6 (6, 8) card_14 = calc11_card_405 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_406_eq : placed 2 (4, 8) card_33 = calc11_card_406 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_407_eq : placed 5 (1, 7) card_322 = calc11_card_407 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_408_eq : inline_816.required ∪ ∅ = calc11_set_408 := by decide +kernel

theorem calc11_set_409_eq : inline_816.envelope ∪ ∅ = calc11_set_409 := by decide +kernel

theorem calc11_set_410_eq : calc11_card_407.required ∪ calc11_set_408 = calc11_set_410 := by decide +kernel

theorem calc11_set_411_eq : calc11_card_407.envelope ∪ calc11_set_409 = calc11_set_411 := by decide +kernel

theorem calc11_set_412_eq : calc11_card_406.required ∪ calc11_set_410 = calc11_set_412 := by decide +kernel

theorem calc11_set_413_eq : calc11_card_406.envelope ∪ calc11_set_411 = calc11_set_413 := by decide +kernel

theorem calc11_set_414_eq : calc11_card_405.required ∪ calc11_set_412 = calc11_set_414 := by decide +kernel

theorem calc11_set_415_eq : calc11_card_405.envelope ∪ calc11_set_413 = calc11_set_415 := by decide +kernel

theorem calc11_set_416_eq : inline_816.envelope ∩ calc11_card_405.envelope = calc11_set_416 := by decide +kernel

theorem calc11_set_417_eq : calc11_card_407.envelope ∩ calc11_set_416 = calc11_set_417 := by decide +kernel

theorem calc11_set_418_eq : calc11_card_406.envelope ∩ calc11_set_417 = calc11_set_418 := by decide +kernel

theorem calc11_set_419_eq : calc11_set_414 ∪ calc11_set_418 = calc11_set_419 := by decide +kernel

theorem calc11_finishA_420 : calc11_set_419.erase (5, 4) = inline_817.required := by decide +kernel

theorem calc11_finishT_420 : insert (5, 4) calc11_set_415 = inline_817.envelope := by decide +kernel

theorem eq_inline_817 : inline_817 = combine (5, 4) [placed 6 (6, 8) card_14, placed 2 (4, 8) card_33, placed 5 (1, 7) card_322, inline_816] := by
  rw [calc11_card_405_eq, calc11_card_406_eq, calc11_card_407_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_408_eq, calc11_set_410_eq, calc11_set_412_eq, calc11_set_414_eq, calc11_set_416_eq, calc11_set_417_eq, calc11_set_418_eq, calc11_set_419_eq, calc11_finishA_420]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_409_eq, calc11_set_411_eq, calc11_set_413_eq, calc11_set_415_eq, calc11_finishT_420]
  · decide +kernel

theorem valid_inline_817 : Valid inline_817 := by
  rw [eq_inline_817]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_322
  subst c
  exact valid_inline_816

theorem calc11_card_421_eq : placed 0 (5, 3) card_7 = calc11_card_421 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_422_eq : placed 1 (4, 4) card_8 = calc11_card_422 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_423_eq : placed 4 (6, 3) card_9 = calc11_card_423 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_424_eq : placed 2 (4, 9) card_485 = calc11_card_424 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_425_eq : calc11_card_424.required ∪ ∅ = calc11_set_425 := by decide +kernel

theorem calc11_set_426_eq : calc11_card_424.envelope ∪ ∅ = calc11_set_426 := by decide +kernel

theorem calc11_set_427_eq : calc11_card_423.required ∪ calc11_set_425 = calc11_set_427 := by decide +kernel

theorem calc11_set_428_eq : calc11_card_423.envelope ∪ calc11_set_426 = calc11_set_428 := by decide +kernel

theorem calc11_set_429_eq : calc11_card_422.required ∪ calc11_set_427 = calc11_set_429 := by decide +kernel

theorem calc11_set_430_eq : calc11_card_422.envelope ∪ calc11_set_428 = calc11_set_430 := by decide +kernel

theorem calc11_set_431_eq : calc11_card_421.required ∪ calc11_set_429 = calc11_set_431 := by decide +kernel

theorem calc11_set_432_eq : calc11_card_421.envelope ∪ calc11_set_430 = calc11_set_432 := by decide +kernel

theorem calc11_set_433_eq : calc11_card_424.envelope ∩ calc11_card_421.envelope = calc11_set_433 := by decide +kernel

theorem calc11_set_434_eq : calc11_card_423.envelope ∩ calc11_set_433 = calc11_set_434 := by decide +kernel

theorem calc11_set_435_eq : calc11_card_422.envelope ∩ calc11_set_434 = calc11_set_435 := by decide +kernel

theorem calc11_set_436_eq : calc11_set_431 ∪ calc11_set_435 = calc11_set_436 := by decide +kernel

theorem calc11_finishA_437 : calc11_set_436.erase (5, 7) = inline_818.required := by decide +kernel

theorem calc11_finishT_437 : insert (5, 7) calc11_set_432 = inline_818.envelope := by decide +kernel

theorem eq_inline_818 : inline_818 = combine (5, 7) [placed 0 (5, 3) card_7, placed 1 (4, 4) card_8, placed 4 (6, 3) card_9, placed 2 (4, 9) card_485] := by
  rw [calc11_card_421_eq, calc11_card_422_eq, calc11_card_423_eq, calc11_card_424_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_425_eq, calc11_set_427_eq, calc11_set_429_eq, calc11_set_431_eq, calc11_set_433_eq, calc11_set_434_eq, calc11_set_435_eq, calc11_set_436_eq, calc11_finishA_437]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_426_eq, calc11_set_428_eq, calc11_set_430_eq, calc11_set_432_eq, calc11_finishT_437]
  · decide +kernel

theorem valid_inline_818 : Valid inline_818 := by
  rw [eq_inline_818]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_9
  subst c
  exact placed_valid 2 (4, 9) valid_485

theorem calc11_card_438_eq : placed 2 (3, 7) card_136 = calc11_card_438 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_439_eq : placed 0 (3, 2) card_267 = calc11_card_439 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_440_eq : placed 5 (1, 7) card_322 = calc11_card_440 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_441_eq : placed 3 (9, 3) card_322 = calc11_card_441 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_442_eq : inline_818.required ∪ ∅ = calc11_set_442 := by decide +kernel

theorem calc11_set_443_eq : inline_818.envelope ∪ ∅ = calc11_set_443 := by decide +kernel

theorem calc11_set_444_eq : calc11_card_441.required ∪ calc11_set_442 = calc11_set_444 := by decide +kernel

theorem calc11_set_445_eq : calc11_card_441.envelope ∪ calc11_set_443 = calc11_set_445 := by decide +kernel

theorem calc11_set_446_eq : calc11_card_440.required ∪ calc11_set_444 = calc11_set_446 := by decide +kernel

theorem calc11_set_447_eq : calc11_card_440.envelope ∪ calc11_set_445 = calc11_set_447 := by decide +kernel

theorem calc11_set_448_eq : calc11_card_439.required ∪ calc11_set_446 = calc11_set_448 := by decide +kernel

theorem calc11_set_449_eq : calc11_card_439.envelope ∪ calc11_set_447 = calc11_set_449 := by decide +kernel

theorem calc11_set_450_eq : calc11_card_438.required ∪ calc11_set_448 = calc11_set_450 := by decide +kernel

theorem calc11_set_451_eq : calc11_card_438.envelope ∪ calc11_set_449 = calc11_set_451 := by decide +kernel

theorem calc11_set_452_eq : inline_818.envelope ∩ calc11_card_438.envelope = calc11_set_452 := by decide +kernel

theorem calc11_set_453_eq : calc11_card_441.envelope ∩ calc11_set_452 = calc11_set_453 := by decide +kernel

theorem calc11_set_454_eq : calc11_card_440.envelope ∩ calc11_set_453 = calc11_set_454 := by decide +kernel

theorem calc11_set_455_eq : calc11_card_439.envelope ∩ calc11_set_454 = calc11_set_455 := by decide +kernel

theorem calc11_set_456_eq : calc11_set_450 ∪ calc11_set_455 = calc11_set_456 := by decide +kernel

theorem calc11_finishA_457 : calc11_set_456.erase (5, 4) = inline_819.required := by decide +kernel

theorem calc11_finishT_457 : insert (5, 4) calc11_set_451 = inline_819.envelope := by decide +kernel

theorem eq_inline_819 : inline_819 = combine (5, 4) [placed 2 (3, 7) card_136, placed 0 (3, 2) card_267, placed 5 (1, 7) card_322, placed 3 (9, 3) card_322, inline_818] := by
  rw [calc11_card_438_eq, calc11_card_439_eq, calc11_card_440_eq, calc11_card_441_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_442_eq, calc11_set_444_eq, calc11_set_446_eq, calc11_set_448_eq, calc11_set_450_eq, calc11_set_452_eq, calc11_set_453_eq, calc11_set_454_eq, calc11_set_455_eq, calc11_set_456_eq, calc11_finishA_457]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_443_eq, calc11_set_445_eq, calc11_set_447_eq, calc11_set_449_eq, calc11_set_451_eq, calc11_finishT_457]
  · decide +kernel

theorem valid_inline_819 : Valid inline_819 := by
  rw [eq_inline_819]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_136
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_267
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_322
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 3) valid_322
  subst c
  exact valid_inline_818

theorem calc11_card_458_eq : placed 4 (6, 3) card_9 = calc11_card_458 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_459_eq : placed 1 (2, 4) card_115 = calc11_card_459 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_460_eq : placed 3 (8, 3) card_302 = calc11_card_460 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_461_eq : placed 3 (8, 3) card_303 = calc11_card_461 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_462_eq : calc11_card_461.required ∪ ∅ = calc11_set_462 := by decide +kernel

theorem calc11_set_463_eq : calc11_card_461.envelope ∪ ∅ = calc11_set_463 := by decide +kernel

theorem calc11_set_464_eq : calc11_card_460.required ∪ calc11_set_462 = calc11_set_464 := by decide +kernel

theorem calc11_set_465_eq : calc11_card_460.envelope ∪ calc11_set_463 = calc11_set_465 := by decide +kernel

theorem calc11_set_466_eq : calc11_card_459.required ∪ calc11_set_464 = calc11_set_466 := by decide +kernel

theorem calc11_set_467_eq : calc11_card_459.envelope ∪ calc11_set_465 = calc11_set_467 := by decide +kernel

theorem calc11_set_468_eq : calc11_card_458.required ∪ calc11_set_466 = calc11_set_468 := by decide +kernel

theorem calc11_set_469_eq : calc11_card_458.envelope ∪ calc11_set_467 = calc11_set_469 := by decide +kernel

theorem calc11_set_470_eq : calc11_card_461.envelope ∩ calc11_card_458.envelope = calc11_set_470 := by decide +kernel

theorem calc11_set_471_eq : calc11_card_460.envelope ∩ calc11_set_470 = calc11_set_471 := by decide +kernel

theorem calc11_set_472_eq : calc11_card_459.envelope ∩ calc11_set_471 = calc11_set_472 := by decide +kernel

theorem calc11_set_473_eq : calc11_set_468 ∪ calc11_set_472 = calc11_set_473 := by decide +kernel

theorem calc11_finishA_474 : calc11_set_473.erase (5, 7) = inline_820.required := by decide +kernel

theorem calc11_finishT_474 : insert (5, 7) calc11_set_469 = inline_820.envelope := by decide +kernel

theorem eq_inline_820 : inline_820 = combine (5, 7) [placed 4 (6, 3) card_9, placed 1 (2, 4) card_115, placed 3 (8, 3) card_302, placed 3 (8, 3) card_303] := by
  rw [calc11_card_458_eq, calc11_card_459_eq, calc11_card_460_eq, calc11_card_461_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_462_eq, calc11_set_464_eq, calc11_set_466_eq, calc11_set_468_eq, calc11_set_470_eq, calc11_set_471_eq, calc11_set_472_eq, calc11_set_473_eq, calc11_finishA_474]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_463_eq, calc11_set_465_eq, calc11_set_467_eq, calc11_set_469_eq, calc11_finishT_474]
  · decide +kernel

theorem valid_inline_820 : Valid inline_820 := by
  rw [eq_inline_820]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_302
  subst c
  exact placed_valid 3 (8, 3) valid_303

theorem calc11_card_475_eq : placed 2 (4, 8) card_13 = calc11_card_475 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_476_eq : placed 6 (6, 8) card_14 = calc11_card_476 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_477_eq : placed 7 (8, 7) card_332 = calc11_card_477 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_478_eq : inline_820.required ∪ ∅ = calc11_set_478 := by decide +kernel

theorem calc11_set_479_eq : inline_820.envelope ∪ ∅ = calc11_set_479 := by decide +kernel

theorem calc11_set_480_eq : calc11_card_477.required ∪ calc11_set_478 = calc11_set_480 := by decide +kernel

theorem calc11_set_481_eq : calc11_card_477.envelope ∪ calc11_set_479 = calc11_set_481 := by decide +kernel

theorem calc11_set_482_eq : calc11_card_476.required ∪ calc11_set_480 = calc11_set_482 := by decide +kernel

theorem calc11_set_483_eq : calc11_card_476.envelope ∪ calc11_set_481 = calc11_set_483 := by decide +kernel

theorem calc11_set_484_eq : calc11_card_475.required ∪ calc11_set_482 = calc11_set_484 := by decide +kernel

theorem calc11_set_485_eq : calc11_card_475.envelope ∪ calc11_set_483 = calc11_set_485 := by decide +kernel

theorem calc11_set_486_eq : inline_820.envelope ∩ calc11_card_475.envelope = calc11_set_486 := by decide +kernel

theorem calc11_set_487_eq : calc11_card_477.envelope ∩ calc11_set_486 = calc11_set_487 := by decide +kernel

theorem calc11_set_488_eq : calc11_card_476.envelope ∩ calc11_set_487 = calc11_set_488 := by decide +kernel

theorem calc11_set_489_eq : calc11_set_484 ∪ calc11_set_488 = calc11_set_489 := by decide +kernel

theorem calc11_finishA_490 : calc11_set_489.erase (5, 4) = inline_821.required := by decide +kernel

theorem calc11_finishT_490 : insert (5, 4) calc11_set_485 = inline_821.envelope := by decide +kernel

theorem eq_inline_821 : inline_821 = combine (5, 4) [placed 2 (4, 8) card_13, placed 6 (6, 8) card_14, placed 7 (8, 7) card_332, inline_820] := by
  rw [calc11_card_475_eq, calc11_card_476_eq, calc11_card_477_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_478_eq, calc11_set_480_eq, calc11_set_482_eq, calc11_set_484_eq, calc11_set_486_eq, calc11_set_487_eq, calc11_set_488_eq, calc11_set_489_eq, calc11_finishA_490]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_479_eq, calc11_set_481_eq, calc11_set_483_eq, calc11_set_485_eq, calc11_finishT_490]
  · decide +kernel

theorem valid_inline_821 : Valid inline_821 := by
  rw [eq_inline_821]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 7) valid_332
  subst c
  exact valid_inline_820

theorem calc11_card_491_eq : placed 4 (6, 3) card_12 = calc11_card_491 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_492_eq : placed 4 (6, 3) card_13 = calc11_card_492 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_493_eq : placed 3 (8, 4) card_118 = calc11_card_493 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_494_eq : placed 6 (6, 10) card_369 = calc11_card_494 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_495_eq : placed 3 (8, 4) card_435 = calc11_card_495 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_496_eq : placed 0 (4, 1) card_528 = calc11_card_496 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_497_eq : placed 1 (1, 3) card_689 = calc11_card_497 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_498_eq : calc11_card_497.required ∪ ∅ = calc11_set_498 := by decide +kernel

theorem calc11_set_499_eq : calc11_card_497.envelope ∪ ∅ = calc11_set_499 := by decide +kernel

theorem calc11_set_500_eq : calc11_card_496.required ∪ calc11_set_498 = calc11_set_500 := by decide +kernel

theorem calc11_set_501_eq : calc11_card_496.envelope ∪ calc11_set_499 = calc11_set_501 := by decide +kernel

theorem calc11_set_502_eq : calc11_card_495.required ∪ calc11_set_500 = calc11_set_502 := by decide +kernel

theorem calc11_set_503_eq : calc11_card_495.envelope ∪ calc11_set_501 = calc11_set_503 := by decide +kernel

theorem calc11_set_504_eq : calc11_card_494.required ∪ calc11_set_502 = calc11_set_504 := by decide +kernel

theorem calc11_set_505_eq : calc11_card_494.envelope ∪ calc11_set_503 = calc11_set_505 := by decide +kernel

theorem calc11_set_506_eq : calc11_card_493.required ∪ calc11_set_504 = calc11_set_506 := by decide +kernel

theorem calc11_set_507_eq : calc11_card_493.envelope ∪ calc11_set_505 = calc11_set_507 := by decide +kernel

theorem calc11_set_508_eq : calc11_card_492.required ∪ calc11_set_506 = calc11_set_508 := by decide +kernel

theorem calc11_set_509_eq : calc11_card_492.envelope ∪ calc11_set_507 = calc11_set_509 := by decide +kernel

theorem calc11_set_510_eq : calc11_card_491.required ∪ calc11_set_508 = calc11_set_510 := by decide +kernel

theorem calc11_set_511_eq : calc11_card_491.envelope ∪ calc11_set_509 = calc11_set_511 := by decide +kernel

theorem calc11_set_512_eq : calc11_card_497.envelope ∩ calc11_card_491.envelope = calc11_set_512 := by decide +kernel

theorem calc11_set_513_eq : calc11_card_496.envelope ∩ calc11_set_512 = calc11_set_513 := by decide +kernel

theorem calc11_set_514_eq : calc11_card_495.envelope ∩ calc11_set_513 = calc11_set_514 := by decide +kernel

theorem calc11_set_515_eq : calc11_card_494.envelope ∩ calc11_set_514 = calc11_set_515 := by decide +kernel

theorem calc11_set_516_eq : calc11_card_493.envelope ∩ calc11_set_515 = calc11_set_516 := by decide +kernel

theorem calc11_set_517_eq : calc11_card_492.envelope ∩ calc11_set_516 = calc11_set_517 := by decide +kernel

theorem calc11_set_518_eq : calc11_set_510 ∪ calc11_set_517 = calc11_set_518 := by decide +kernel

theorem calc11_finishA_519 : calc11_set_518.erase (5, 7) = inline_822.required := by decide +kernel

theorem calc11_finishT_519 : insert (5, 7) calc11_set_511 = inline_822.envelope := by decide +kernel

theorem eq_inline_822 : inline_822 = combine (5, 7) [placed 4 (6, 3) card_12, placed 4 (6, 3) card_13, placed 3 (8, 4) card_118, placed 6 (6, 10) card_369, placed 3 (8, 4) card_435, placed 0 (4, 1) card_528, placed 1 (1, 3) card_689] := by
  rw [calc11_card_491_eq, calc11_card_492_eq, calc11_card_493_eq, calc11_card_494_eq, calc11_card_495_eq, calc11_card_496_eq, calc11_card_497_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_498_eq, calc11_set_500_eq, calc11_set_502_eq, calc11_set_504_eq, calc11_set_506_eq, calc11_set_508_eq, calc11_set_510_eq, calc11_set_512_eq, calc11_set_513_eq, calc11_set_514_eq, calc11_set_515_eq, calc11_set_516_eq, calc11_set_517_eq, calc11_set_518_eq, calc11_finishA_519]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_499_eq, calc11_set_501_eq, calc11_set_503_eq, calc11_set_505_eq, calc11_set_507_eq, calc11_set_509_eq, calc11_set_511_eq, calc11_finishT_519]
  · decide +kernel

theorem valid_inline_822 : Valid inline_822 := by
  rw [eq_inline_822]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_118
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 10) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_528
  subst c
  exact placed_valid 1 (1, 3) valid_689

theorem calc11_card_520_eq : placed 3 (8, 4) card_537 = calc11_card_520 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_521_eq : placed 2 (3, 9) card_537 = calc11_card_521 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_522_eq : placed 3 (7, 4) card_702 = calc11_card_522 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_523_eq : placed 2 (3, 8) card_702 = calc11_card_523 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_524_eq : placed 1 (0, 4) card_704 = calc11_card_524 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_525_eq : placed 0 (3, 1) card_704 = calc11_card_525 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_526_eq : calc11_card_525.required ∪ ∅ = calc11_set_526 := by decide +kernel

theorem calc11_set_527_eq : calc11_card_525.envelope ∪ ∅ = calc11_set_527 := by decide +kernel

theorem calc11_set_528_eq : calc11_card_524.required ∪ calc11_set_526 = calc11_set_528 := by decide +kernel

theorem calc11_set_529_eq : calc11_card_524.envelope ∪ calc11_set_527 = calc11_set_529 := by decide +kernel

theorem calc11_set_530_eq : calc11_card_523.required ∪ calc11_set_528 = calc11_set_530 := by decide +kernel

theorem calc11_set_531_eq : calc11_card_523.envelope ∪ calc11_set_529 = calc11_set_531 := by decide +kernel

theorem calc11_set_532_eq : calc11_card_522.required ∪ calc11_set_530 = calc11_set_532 := by decide +kernel

theorem calc11_set_533_eq : calc11_card_522.envelope ∪ calc11_set_531 = calc11_set_533 := by decide +kernel

theorem calc11_set_534_eq : calc11_card_521.required ∪ calc11_set_532 = calc11_set_534 := by decide +kernel

theorem calc11_set_535_eq : calc11_card_521.envelope ∪ calc11_set_533 = calc11_set_535 := by decide +kernel

theorem calc11_set_536_eq : calc11_card_520.required ∪ calc11_set_534 = calc11_set_536 := by decide +kernel

theorem calc11_set_537_eq : calc11_card_520.envelope ∪ calc11_set_535 = calc11_set_537 := by decide +kernel

theorem calc11_set_538_eq : calc11_card_525.envelope ∩ calc11_card_520.envelope = calc11_set_538 := by decide +kernel

theorem calc11_set_539_eq : calc11_card_524.envelope ∩ calc11_set_538 = calc11_set_539 := by decide +kernel

theorem calc11_set_540_eq : calc11_card_523.envelope ∩ calc11_set_539 = calc11_set_540 := by decide +kernel

theorem calc11_set_541_eq : calc11_card_522.envelope ∩ calc11_set_540 = calc11_set_541 := by decide +kernel

theorem calc11_set_542_eq : calc11_card_521.envelope ∩ calc11_set_541 = calc11_set_542 := by decide +kernel

theorem calc11_set_543_eq : calc11_set_536 ∪ calc11_set_542 = calc11_set_543 := by decide +kernel

theorem calc11_finishA_544 : calc11_set_543.erase (4, 6) = inline_823.required := by decide +kernel

theorem calc11_finishT_544 : insert (4, 6) calc11_set_537 = inline_823.envelope := by decide +kernel

theorem eq_inline_823 : inline_823 = combine (4, 6) [placed 3 (8, 4) card_537, placed 2 (3, 9) card_537, placed 3 (7, 4) card_702, placed 2 (3, 8) card_702, placed 1 (0, 4) card_704, placed 0 (3, 1) card_704] := by
  rw [calc11_card_520_eq, calc11_card_521_eq, calc11_card_522_eq, calc11_card_523_eq, calc11_card_524_eq, calc11_card_525_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_526_eq, calc11_set_528_eq, calc11_set_530_eq, calc11_set_532_eq, calc11_set_534_eq, calc11_set_536_eq, calc11_set_538_eq, calc11_set_539_eq, calc11_set_540_eq, calc11_set_541_eq, calc11_set_542_eq, calc11_set_543_eq, calc11_finishA_544]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_527_eq, calc11_set_529_eq, calc11_set_531_eq, calc11_set_533_eq, calc11_set_535_eq, calc11_set_537_eq, calc11_finishT_544]
  · decide +kernel

theorem valid_inline_823 : Valid inline_823 := by
  rw [eq_inline_823]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_537
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_537
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_702
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_702
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_704
  subst c
  exact placed_valid 0 (3, 1) valid_704

theorem calc11_card_545_eq : placed 0 (4, 1) card_459 = calc11_card_545 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_546_eq : placed 2 (3, 10) card_535 = calc11_card_546 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_547_eq : placed 0 (1, 1) card_617 = calc11_card_547 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_548_eq : placed 1 (0, 1) card_660 = calc11_card_548 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_549_eq : placed 1 (0, 3) card_663 = calc11_card_549 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_550_eq : placed 2 (2, 10) card_705 = calc11_card_550 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_551_eq : placed 2 (0, 10) card_706 = calc11_card_551 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_552_eq : calc11_card_551.required ∪ ∅ = calc11_set_552 := by decide +kernel

theorem calc11_set_553_eq : calc11_card_551.envelope ∪ ∅ = calc11_set_553 := by decide +kernel

theorem calc11_set_554_eq : calc11_card_550.required ∪ calc11_set_552 = calc11_set_554 := by decide +kernel

theorem calc11_set_555_eq : calc11_card_550.envelope ∪ calc11_set_553 = calc11_set_555 := by decide +kernel

theorem calc11_set_556_eq : inline_823.required ∪ calc11_set_554 = calc11_set_556 := by decide +kernel

theorem calc11_set_557_eq : inline_823.envelope ∪ calc11_set_555 = calc11_set_557 := by decide +kernel

theorem calc11_set_558_eq : inline_822.required ∪ calc11_set_556 = calc11_set_558 := by decide +kernel

theorem calc11_set_559_eq : inline_822.envelope ∪ calc11_set_557 = calc11_set_559 := by decide +kernel

theorem calc11_set_560_eq : inline_821.required ∪ calc11_set_558 = calc11_set_560 := by decide +kernel

theorem calc11_set_561_eq : inline_821.envelope ∪ calc11_set_559 = calc11_set_561 := by decide +kernel

theorem calc11_set_562_eq : inline_819.required ∪ calc11_set_560 = calc11_set_562 := by decide +kernel

theorem calc11_set_563_eq : inline_819.envelope ∪ calc11_set_561 = calc11_set_563 := by decide +kernel

theorem calc11_set_564_eq : inline_817.required ∪ calc11_set_562 = calc11_set_564 := by decide +kernel

theorem calc11_set_565_eq : inline_817.envelope ∪ calc11_set_563 = calc11_set_565 := by decide +kernel

theorem calc11_set_566_eq : inline_815.required ∪ calc11_set_564 = calc11_set_566 := by decide +kernel

theorem calc11_set_567_eq : inline_815.envelope ∪ calc11_set_565 = calc11_set_567 := by decide +kernel

theorem calc11_set_568_eq : calc11_card_549.required ∪ calc11_set_566 = calc11_set_568 := by decide +kernel

theorem calc11_set_569_eq : calc11_card_549.envelope ∪ calc11_set_567 = calc11_set_569 := by decide +kernel

theorem calc11_set_570_eq : calc11_card_548.required ∪ calc11_set_568 = calc11_set_570 := by decide +kernel

theorem calc11_set_571_eq : calc11_card_548.envelope ∪ calc11_set_569 = calc11_set_571 := by decide +kernel

theorem calc11_set_572_eq : calc11_card_547.required ∪ calc11_set_570 = calc11_set_572 := by decide +kernel

theorem calc11_set_573_eq : calc11_card_547.envelope ∪ calc11_set_571 = calc11_set_573 := by decide +kernel

theorem calc11_set_574_eq : calc11_card_546.required ∪ calc11_set_572 = calc11_set_574 := by decide +kernel

theorem calc11_set_575_eq : calc11_card_546.envelope ∪ calc11_set_573 = calc11_set_575 := by decide +kernel

theorem calc11_set_576_eq : calc11_card_545.required ∪ calc11_set_574 = calc11_set_576 := by decide +kernel

theorem calc11_set_577_eq : calc11_card_545.envelope ∪ calc11_set_575 = calc11_set_577 := by decide +kernel

theorem calc11_set_578_eq : calc11_card_551.envelope ∩ calc11_card_545.envelope = calc11_set_578 := by decide +kernel

theorem calc11_set_579_eq : calc11_card_550.envelope ∩ calc11_set_578 = calc11_set_579 := by decide +kernel

theorem calc11_set_580_eq : inline_823.envelope ∩ calc11_set_579 = calc11_set_580 := by decide +kernel

theorem calc11_set_581_eq : inline_822.envelope ∩ calc11_set_580 = calc11_set_581 := by decide +kernel

theorem calc11_set_582_eq : inline_821.envelope ∩ calc11_set_581 = calc11_set_582 := by decide +kernel

theorem calc11_set_583_eq : inline_819.envelope ∩ calc11_set_582 = calc11_set_583 := by decide +kernel

theorem calc11_set_584_eq : inline_817.envelope ∩ calc11_set_583 = calc11_set_584 := by decide +kernel

theorem calc11_set_585_eq : inline_815.envelope ∩ calc11_set_584 = calc11_set_585 := by decide +kernel

theorem calc11_set_586_eq : calc11_card_549.envelope ∩ calc11_set_585 = calc11_set_586 := by decide +kernel

theorem calc11_set_587_eq : calc11_card_548.envelope ∩ calc11_set_586 = calc11_set_587 := by decide +kernel

theorem calc11_set_588_eq : calc11_card_547.envelope ∩ calc11_set_587 = calc11_set_588 := by decide +kernel

theorem calc11_set_589_eq : calc11_card_546.envelope ∩ calc11_set_588 = calc11_set_589 := by decide +kernel

theorem calc11_set_590_eq : calc11_set_576 ∪ calc11_set_589 = calc11_set_590 := by decide +kernel

theorem calc11_finishA_591 : calc11_set_590.erase (5, 6) = card_707.required := by decide +kernel

theorem calc11_finishT_591 : insert (5, 6) calc11_set_577 = card_707.envelope := by decide +kernel

theorem eq_card_707 : card_707 = combine (5, 6) [placed 0 (4, 1) card_459, placed 2 (3, 10) card_535, placed 0 (1, 1) card_617, placed 1 (0, 1) card_660, placed 1 (0, 3) card_663, inline_815, inline_817, inline_819, inline_821, inline_822, inline_823, placed 2 (2, 10) card_705, placed 2 (0, 10) card_706] := by
  rw [calc11_card_545_eq, calc11_card_546_eq, calc11_card_547_eq, calc11_card_548_eq, calc11_card_549_eq, calc11_card_550_eq, calc11_card_551_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_552_eq, calc11_set_554_eq, calc11_set_556_eq, calc11_set_558_eq, calc11_set_560_eq, calc11_set_562_eq, calc11_set_564_eq, calc11_set_566_eq, calc11_set_568_eq, calc11_set_570_eq, calc11_set_572_eq, calc11_set_574_eq, calc11_set_576_eq, calc11_set_578_eq, calc11_set_579_eq, calc11_set_580_eq, calc11_set_581_eq, calc11_set_582_eq, calc11_set_583_eq, calc11_set_584_eq, calc11_set_585_eq, calc11_set_586_eq, calc11_set_587_eq, calc11_set_588_eq, calc11_set_589_eq, calc11_set_590_eq, calc11_finishA_591]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_553_eq, calc11_set_555_eq, calc11_set_557_eq, calc11_set_559_eq, calc11_set_561_eq, calc11_set_563_eq, calc11_set_565_eq, calc11_set_567_eq, calc11_set_569_eq, calc11_set_571_eq, calc11_set_573_eq, calc11_set_575_eq, calc11_set_577_eq, calc11_finishT_591]
  · decide +kernel

theorem valid_707 : Valid card_707 := by
  rw [eq_card_707]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_459
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 10) valid_535
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_617
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_660
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_663
  rcases hc with rfl | hc
  · exact valid_inline_815
  rcases hc with rfl | hc
  · exact valid_inline_817
  rcases hc with rfl | hc
  · exact valid_inline_819
  rcases hc with rfl | hc
  · exact valid_inline_821
  rcases hc with rfl | hc
  · exact valid_inline_822
  rcases hc with rfl | hc
  · exact valid_inline_823
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 10) valid_705
  subst c
  exact placed_valid 2 (0, 10) valid_706

theorem calc11_card_592_eq : placed 3 (9, 8) card_7 = calc11_card_592 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_593_eq : placed 1 (4, 7) card_234 = calc11_card_593 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_594_eq : placed 3 (9, 7) card_241 = calc11_card_594 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_595_eq : calc11_card_594.required ∪ ∅ = calc11_set_595 := by decide +kernel

theorem calc11_set_596_eq : calc11_card_594.envelope ∪ ∅ = calc11_set_596 := by decide +kernel

theorem calc11_set_597_eq : calc11_card_593.required ∪ calc11_set_595 = calc11_set_597 := by decide +kernel

theorem calc11_set_598_eq : calc11_card_593.envelope ∪ calc11_set_596 = calc11_set_598 := by decide +kernel

theorem calc11_set_599_eq : calc11_card_592.required ∪ calc11_set_597 = calc11_set_599 := by decide +kernel

theorem calc11_set_600_eq : calc11_card_592.envelope ∪ calc11_set_598 = calc11_set_600 := by decide +kernel

theorem calc11_set_601_eq : calc11_card_594.envelope ∩ calc11_card_592.envelope = calc11_set_601 := by decide +kernel

theorem calc11_set_602_eq : calc11_card_593.envelope ∩ calc11_set_601 = calc11_set_602 := by decide +kernel

theorem calc11_set_603_eq : calc11_set_599 ∪ calc11_set_602 = calc11_set_603 := by decide +kernel

theorem calc11_finishA_604 : calc11_set_603.erase (5, 8) = inline_824.required := by decide +kernel

theorem calc11_finishT_604 : insert (5, 8) calc11_set_600 = inline_824.envelope := by decide +kernel

theorem eq_inline_824 : inline_824 = combine (5, 8) [placed 3 (9, 8) card_7, placed 1 (4, 7) card_234, placed 3 (9, 7) card_241] := by
  rw [calc11_card_592_eq, calc11_card_593_eq, calc11_card_594_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_595_eq, calc11_set_597_eq, calc11_set_599_eq, calc11_set_601_eq, calc11_set_602_eq, calc11_set_603_eq, calc11_finishA_604]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_596_eq, calc11_set_598_eq, calc11_set_600_eq, calc11_finishT_604]
  · decide +kernel

theorem valid_inline_824 : Valid inline_824 := by
  rw [eq_inline_824]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 8) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 7) valid_234
  subst c
  exact placed_valid 3 (9, 7) valid_241

theorem calc11_card_605_eq : placed 4 (7, 5) card_7 = calc11_card_605 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_606_eq : placed 0 (6, 5) card_9 = calc11_card_606 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_607_eq : placed 3 (9, 6) card_92 = calc11_card_607 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_608_eq : calc11_card_607.required ∪ ∅ = calc11_set_608 := by decide +kernel

theorem calc11_set_609_eq : calc11_card_607.envelope ∪ ∅ = calc11_set_609 := by decide +kernel

theorem calc11_set_610_eq : calc11_card_606.required ∪ calc11_set_608 = calc11_set_610 := by decide +kernel

theorem calc11_set_611_eq : calc11_card_606.envelope ∪ calc11_set_609 = calc11_set_611 := by decide +kernel

theorem calc11_set_612_eq : calc11_card_605.required ∪ calc11_set_610 = calc11_set_612 := by decide +kernel

theorem calc11_set_613_eq : calc11_card_605.envelope ∪ calc11_set_611 = calc11_set_613 := by decide +kernel

theorem calc11_set_614_eq : calc11_card_607.envelope ∩ calc11_card_605.envelope = calc11_set_614 := by decide +kernel

theorem calc11_set_615_eq : calc11_card_606.envelope ∩ calc11_set_614 = calc11_set_615 := by decide +kernel

theorem calc11_set_616_eq : calc11_set_612 ∪ calc11_set_615 = calc11_set_616 := by decide +kernel

theorem calc11_finishA_617 : calc11_set_616.erase (7, 9) = inline_825.required := by decide +kernel

theorem calc11_finishT_617 : insert (7, 9) calc11_set_613 = inline_825.envelope := by decide +kernel

theorem eq_inline_825 : inline_825 = combine (7, 9) [placed 4 (7, 5) card_7, placed 0 (6, 5) card_9, placed 3 (9, 6) card_92] := by
  rw [calc11_card_605_eq, calc11_card_606_eq, calc11_card_607_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_608_eq, calc11_set_610_eq, calc11_set_612_eq, calc11_set_614_eq, calc11_set_615_eq, calc11_set_616_eq, calc11_finishA_617]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_609_eq, calc11_set_611_eq, calc11_set_613_eq, calc11_finishT_617]
  · decide +kernel

theorem valid_inline_825 : Valid inline_825 := by
  rw [eq_inline_825]
  apply combination_rule (7, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 5) valid_9
  subst c
  exact placed_valid 3 (9, 6) valid_92

theorem calc11_card_618_eq : placed 4 (7, 5) card_44 = calc11_card_618 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_619_eq : placed 0 (7, 5) card_52 = calc11_card_619 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_620_eq : inline_825.required ∪ ∅ = calc11_set_620 := by decide +kernel

theorem calc11_set_621_eq : inline_825.envelope ∪ ∅ = calc11_set_621 := by decide +kernel

theorem calc11_set_622_eq : calc11_card_619.required ∪ calc11_set_620 = calc11_set_622 := by decide +kernel

theorem calc11_set_623_eq : calc11_card_619.envelope ∪ calc11_set_621 = calc11_set_623 := by decide +kernel

theorem calc11_set_624_eq : calc11_card_618.required ∪ calc11_set_622 = calc11_set_624 := by decide +kernel

theorem calc11_set_625_eq : calc11_card_618.envelope ∪ calc11_set_623 = calc11_set_625 := by decide +kernel

theorem calc11_set_626_eq : inline_825.envelope ∩ calc11_card_618.envelope = calc11_set_626 := by decide +kernel

theorem calc11_set_627_eq : calc11_card_619.envelope ∩ calc11_set_626 = calc11_set_627 := by decide +kernel

theorem calc11_set_628_eq : calc11_set_624 ∪ calc11_set_627 = calc11_set_628 := by decide +kernel

theorem calc11_finishA_629 : calc11_set_628.erase (7, 6) = inline_826.required := by decide +kernel

theorem calc11_finishT_629 : insert (7, 6) calc11_set_625 = inline_826.envelope := by decide +kernel

theorem eq_inline_826 : inline_826 = combine (7, 6) [placed 4 (7, 5) card_44, placed 0 (7, 5) card_52, inline_825] := by
  rw [calc11_card_618_eq, calc11_card_619_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_620_eq, calc11_set_622_eq, calc11_set_624_eq, calc11_set_626_eq, calc11_set_627_eq, calc11_set_628_eq, calc11_finishA_629]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_621_eq, calc11_set_623_eq, calc11_set_625_eq, calc11_finishT_629]
  · decide +kernel

theorem valid_inline_826 : Valid inline_826 := by
  rw [eq_inline_826]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (7, 5) valid_52
  subst c
  exact valid_inline_825

theorem calc11_card_630_eq : placed 4 (9, 5) card_57 = calc11_card_630 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_631_eq : placed 4 (9, 5) card_88 = calc11_card_631 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_632_eq : placed 4 (9, 5) card_111 = calc11_card_632 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_633_eq : placed 0 (5, 5) card_213 = calc11_card_633 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_634_eq : inline_826.required ∪ ∅ = calc11_set_634 := by decide +kernel

theorem calc11_set_635_eq : inline_826.envelope ∪ ∅ = calc11_set_635 := by decide +kernel

theorem calc11_set_636_eq : inline_824.required ∪ calc11_set_634 = calc11_set_636 := by decide +kernel

theorem calc11_set_637_eq : inline_824.envelope ∪ calc11_set_635 = calc11_set_637 := by decide +kernel

theorem calc11_set_638_eq : calc11_card_633.required ∪ calc11_set_636 = calc11_set_638 := by decide +kernel

theorem calc11_set_639_eq : calc11_card_633.envelope ∪ calc11_set_637 = calc11_set_639 := by decide +kernel

theorem calc11_set_640_eq : calc11_card_632.required ∪ calc11_set_638 = calc11_set_640 := by decide +kernel

theorem calc11_set_641_eq : calc11_card_632.envelope ∪ calc11_set_639 = calc11_set_641 := by decide +kernel

theorem calc11_set_642_eq : calc11_card_631.required ∪ calc11_set_640 = calc11_set_642 := by decide +kernel

theorem calc11_set_643_eq : calc11_card_631.envelope ∪ calc11_set_641 = calc11_set_643 := by decide +kernel

theorem calc11_set_644_eq : calc11_card_630.required ∪ calc11_set_642 = calc11_set_644 := by decide +kernel

theorem calc11_set_645_eq : calc11_card_630.envelope ∪ calc11_set_643 = calc11_set_645 := by decide +kernel

theorem calc11_set_646_eq : inline_826.envelope ∩ calc11_card_630.envelope = calc11_set_646 := by decide +kernel

theorem calc11_set_647_eq : inline_824.envelope ∩ calc11_set_646 = calc11_set_647 := by decide +kernel

theorem calc11_set_648_eq : calc11_card_633.envelope ∩ calc11_set_647 = calc11_set_648 := by decide +kernel

theorem calc11_set_649_eq : calc11_card_632.envelope ∩ calc11_set_648 = calc11_set_649 := by decide +kernel

theorem calc11_set_650_eq : calc11_card_631.envelope ∩ calc11_set_649 = calc11_set_650 := by decide +kernel

theorem calc11_set_651_eq : calc11_set_644 ∪ calc11_set_650 = calc11_set_651 := by decide +kernel

theorem calc11_finishA_652 : calc11_set_651.erase (7, 7) = inline_827.required := by decide +kernel

theorem calc11_finishT_652 : insert (7, 7) calc11_set_645 = inline_827.envelope := by decide +kernel

theorem eq_inline_827 : inline_827 = combine (7, 7) [placed 4 (9, 5) card_57, placed 4 (9, 5) card_88, placed 4 (9, 5) card_111, placed 0 (5, 5) card_213, inline_824, inline_826] := by
  rw [calc11_card_630_eq, calc11_card_631_eq, calc11_card_632_eq, calc11_card_633_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_634_eq, calc11_set_636_eq, calc11_set_638_eq, calc11_set_640_eq, calc11_set_642_eq, calc11_set_644_eq, calc11_set_646_eq, calc11_set_647_eq, calc11_set_648_eq, calc11_set_649_eq, calc11_set_650_eq, calc11_set_651_eq, calc11_finishA_652]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_635_eq, calc11_set_637_eq, calc11_set_639_eq, calc11_set_641_eq, calc11_set_643_eq, calc11_set_645_eq, calc11_finishT_652]
  · decide +kernel

theorem valid_inline_827 : Valid inline_827 := by
  rw [eq_inline_827]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 5) valid_57
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 5) valid_88
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 5) valid_111
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 5) valid_213
  rcases hc with rfl | hc
  · exact valid_inline_824
  subst c
  exact valid_inline_826

theorem calc11_card_653_eq : placed 5 (5, 8) card_7 = calc11_card_653 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_654_eq : placed 3 (11, 7) card_186 = calc11_card_654 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_655_eq : placed 6 (9, 11) card_292 = calc11_card_655 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_656_eq : calc11_card_655.required ∪ ∅ = calc11_set_656 := by decide +kernel

theorem calc11_set_657_eq : calc11_card_655.envelope ∪ ∅ = calc11_set_657 := by decide +kernel

theorem calc11_set_658_eq : calc11_card_654.required ∪ calc11_set_656 = calc11_set_658 := by decide +kernel

theorem calc11_set_659_eq : calc11_card_654.envelope ∪ calc11_set_657 = calc11_set_659 := by decide +kernel

theorem calc11_set_660_eq : calc11_card_653.required ∪ calc11_set_658 = calc11_set_660 := by decide +kernel

theorem calc11_set_661_eq : calc11_card_653.envelope ∪ calc11_set_659 = calc11_set_661 := by decide +kernel

theorem calc11_set_662_eq : calc11_card_655.envelope ∩ calc11_card_653.envelope = calc11_set_662 := by decide +kernel

theorem calc11_set_663_eq : calc11_card_654.envelope ∩ calc11_set_662 = calc11_set_663 := by decide +kernel

theorem calc11_set_664_eq : calc11_set_660 ∪ calc11_set_663 = calc11_set_664 := by decide +kernel

theorem calc11_finishA_665 : calc11_set_664.erase (9, 8) = inline_828.required := by decide +kernel

theorem calc11_finishT_665 : insert (9, 8) calc11_set_661 = inline_828.envelope := by decide +kernel

theorem eq_inline_828 : inline_828 = combine (9, 8) [placed 5 (5, 8) card_7, placed 3 (11, 7) card_186, placed 6 (9, 11) card_292] := by
  rw [calc11_card_653_eq, calc11_card_654_eq, calc11_card_655_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_656_eq, calc11_set_658_eq, calc11_set_660_eq, calc11_set_662_eq, calc11_set_663_eq, calc11_set_664_eq, calc11_finishA_665]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_657_eq, calc11_set_659_eq, calc11_set_661_eq, calc11_finishT_665]
  · decide +kernel

theorem valid_inline_828 : Valid inline_828 := by
  rw [eq_inline_828]
  apply combination_rule (9, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 8) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 3 (11, 7) valid_186
  subst c
  exact placed_valid 6 (9, 11) valid_292

theorem calc11_card_666_eq : placed 0 (5, 5) card_117 = calc11_card_666 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_667_eq : placed 4 (9, 6) card_137 = calc11_card_667 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_668_eq : placed 4 (9, 6) card_181 = calc11_card_668 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_669_eq : placed 4 (9, 5) card_257 = calc11_card_669 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_670_eq : placed 4 (9, 5) card_435 = calc11_card_670 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_671_eq : inline_828.required ∪ ∅ = calc11_set_671 := by decide +kernel

theorem calc11_set_672_eq : inline_828.envelope ∪ ∅ = calc11_set_672 := by decide +kernel

theorem calc11_set_673_eq : inline_827.required ∪ calc11_set_671 = calc11_set_673 := by decide +kernel

theorem calc11_set_674_eq : inline_827.envelope ∪ calc11_set_672 = calc11_set_674 := by decide +kernel

theorem calc11_set_675_eq : calc11_card_670.required ∪ calc11_set_673 = calc11_set_675 := by decide +kernel

theorem calc11_set_676_eq : calc11_card_670.envelope ∪ calc11_set_674 = calc11_set_676 := by decide +kernel

theorem calc11_set_677_eq : calc11_card_669.required ∪ calc11_set_675 = calc11_set_677 := by decide +kernel

theorem calc11_set_678_eq : calc11_card_669.envelope ∪ calc11_set_676 = calc11_set_678 := by decide +kernel

theorem calc11_set_679_eq : calc11_card_668.required ∪ calc11_set_677 = calc11_set_679 := by decide +kernel

theorem calc11_set_680_eq : calc11_card_668.envelope ∪ calc11_set_678 = calc11_set_680 := by decide +kernel

theorem calc11_set_681_eq : calc11_card_667.required ∪ calc11_set_679 = calc11_set_681 := by decide +kernel

theorem calc11_set_682_eq : calc11_card_667.envelope ∪ calc11_set_680 = calc11_set_682 := by decide +kernel

theorem calc11_set_683_eq : calc11_card_666.required ∪ calc11_set_681 = calc11_set_683 := by decide +kernel

theorem calc11_set_684_eq : calc11_card_666.envelope ∪ calc11_set_682 = calc11_set_684 := by decide +kernel

theorem calc11_set_685_eq : inline_828.envelope ∩ calc11_card_666.envelope = calc11_set_685 := by decide +kernel

theorem calc11_set_686_eq : inline_827.envelope ∩ calc11_set_685 = calc11_set_686 := by decide +kernel

theorem calc11_set_687_eq : calc11_card_670.envelope ∩ calc11_set_686 = calc11_set_687 := by decide +kernel

theorem calc11_set_688_eq : calc11_card_669.envelope ∩ calc11_set_687 = calc11_set_688 := by decide +kernel

theorem calc11_set_689_eq : calc11_card_668.envelope ∩ calc11_set_688 = calc11_set_689 := by decide +kernel

theorem calc11_set_690_eq : calc11_card_667.envelope ∩ calc11_set_689 = calc11_set_690 := by decide +kernel

theorem calc11_set_691_eq : calc11_set_683 ∪ calc11_set_690 = calc11_set_691 := by decide +kernel

theorem calc11_finishA_692 : calc11_set_691.erase (6, 8) = inline_829.required := by decide +kernel

theorem calc11_finishT_692 : insert (6, 8) calc11_set_684 = inline_829.envelope := by decide +kernel

theorem eq_inline_829 : inline_829 = combine (6, 8) [placed 0 (5, 5) card_117, placed 4 (9, 6) card_137, placed 4 (9, 6) card_181, placed 4 (9, 5) card_257, placed 4 (9, 5) card_435, inline_827, inline_828] := by
  rw [calc11_card_666_eq, calc11_card_667_eq, calc11_card_668_eq, calc11_card_669_eq, calc11_card_670_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_671_eq, calc11_set_673_eq, calc11_set_675_eq, calc11_set_677_eq, calc11_set_679_eq, calc11_set_681_eq, calc11_set_683_eq, calc11_set_685_eq, calc11_set_686_eq, calc11_set_687_eq, calc11_set_688_eq, calc11_set_689_eq, calc11_set_690_eq, calc11_set_691_eq, calc11_finishA_692]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_672_eq, calc11_set_674_eq, calc11_set_676_eq, calc11_set_678_eq, calc11_set_680_eq, calc11_set_682_eq, calc11_set_684_eq, calc11_finishT_692]
  · decide +kernel

theorem valid_inline_829 : Valid inline_829 := by
  rw [eq_inline_829]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 5) valid_117
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 6) valid_137
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 6) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 5) valid_257
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 5) valid_435
  rcases hc with rfl | hc
  · exact valid_inline_827
  subst c
  exact valid_inline_828

theorem calc11_card_693_eq : placed 5 (5, 9) card_12 = calc11_card_693 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_694_eq : placed 3 (11, 6) card_135 = calc11_card_694 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_695_eq : placed 0 (6, 6) card_181 = calc11_card_695 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_696_eq : placed 2 (6, 11) card_435 = calc11_card_696 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_697_eq : placed 2 (5, 11) card_565 = calc11_card_697 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_698_eq : placed 4 (12, 4) card_687 = calc11_card_698 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_699_eq : placed 0 (5, 4) card_689 = calc11_card_699 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_700_eq : calc11_card_699.required ∪ ∅ = calc11_set_700 := by decide +kernel

theorem calc11_set_701_eq : calc11_card_699.envelope ∪ ∅ = calc11_set_701 := by decide +kernel

theorem calc11_set_702_eq : calc11_card_698.required ∪ calc11_set_700 = calc11_set_702 := by decide +kernel

theorem calc11_set_703_eq : calc11_card_698.envelope ∪ calc11_set_701 = calc11_set_703 := by decide +kernel

theorem calc11_set_704_eq : calc11_card_697.required ∪ calc11_set_702 = calc11_set_704 := by decide +kernel

theorem calc11_set_705_eq : calc11_card_697.envelope ∪ calc11_set_703 = calc11_set_705 := by decide +kernel

theorem calc11_set_706_eq : calc11_card_696.required ∪ calc11_set_704 = calc11_set_706 := by decide +kernel

theorem calc11_set_707_eq : calc11_card_696.envelope ∪ calc11_set_705 = calc11_set_707 := by decide +kernel

theorem calc11_set_708_eq : calc11_card_695.required ∪ calc11_set_706 = calc11_set_708 := by decide +kernel

theorem calc11_set_709_eq : calc11_card_695.envelope ∪ calc11_set_707 = calc11_set_709 := by decide +kernel

theorem calc11_set_710_eq : calc11_card_694.required ∪ calc11_set_708 = calc11_set_710 := by decide +kernel

theorem calc11_set_711_eq : calc11_card_694.envelope ∪ calc11_set_709 = calc11_set_711 := by decide +kernel

theorem calc11_set_712_eq : calc11_card_693.required ∪ calc11_set_710 = calc11_set_712 := by decide +kernel

theorem calc11_set_713_eq : calc11_card_693.envelope ∪ calc11_set_711 = calc11_set_713 := by decide +kernel

theorem calc11_set_714_eq : calc11_card_699.envelope ∩ calc11_card_693.envelope = calc11_set_714 := by decide +kernel

theorem calc11_set_715_eq : calc11_card_698.envelope ∩ calc11_set_714 = calc11_set_715 := by decide +kernel

theorem calc11_set_716_eq : calc11_card_697.envelope ∩ calc11_set_715 = calc11_set_716 := by decide +kernel

theorem calc11_set_717_eq : calc11_card_696.envelope ∩ calc11_set_716 = calc11_set_717 := by decide +kernel

theorem calc11_set_718_eq : calc11_card_695.envelope ∩ calc11_set_717 = calc11_set_718 := by decide +kernel

theorem calc11_set_719_eq : calc11_card_694.envelope ∩ calc11_set_718 = calc11_set_719 := by decide +kernel

theorem calc11_set_720_eq : calc11_set_712 ∪ calc11_set_719 = calc11_set_720 := by decide +kernel

theorem calc11_finishA_721 : calc11_set_720.erase (9, 8) = inline_830.required := by decide +kernel

theorem calc11_finishT_721 : insert (9, 8) calc11_set_713 = inline_830.envelope := by decide +kernel

theorem eq_inline_830 : inline_830 = combine (9, 8) [placed 5 (5, 9) card_12, placed 3 (11, 6) card_135, placed 0 (6, 6) card_181, placed 2 (6, 11) card_435, placed 2 (5, 11) card_565, placed 4 (12, 4) card_687, placed 0 (5, 4) card_689] := by
  rw [calc11_card_693_eq, calc11_card_694_eq, calc11_card_695_eq, calc11_card_696_eq, calc11_card_697_eq, calc11_card_698_eq, calc11_card_699_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_700_eq, calc11_set_702_eq, calc11_set_704_eq, calc11_set_706_eq, calc11_set_708_eq, calc11_set_710_eq, calc11_set_712_eq, calc11_set_714_eq, calc11_set_715_eq, calc11_set_716_eq, calc11_set_717_eq, calc11_set_718_eq, calc11_set_719_eq, calc11_set_720_eq, calc11_finishA_721]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_701_eq, calc11_set_703_eq, calc11_set_705_eq, calc11_set_707_eq, calc11_set_709_eq, calc11_set_711_eq, calc11_set_713_eq, calc11_finishT_721]
  · decide +kernel

theorem valid_inline_830 : Valid inline_830 := by
  rw [eq_inline_830]
  apply combination_rule (9, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 9) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 3 (11, 6) valid_135
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 6) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 11) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 11) valid_565
  rcases hc with rfl | hc
  · exact placed_valid 4 (12, 4) valid_687
  subst c
  exact placed_valid 0 (5, 4) valid_689

theorem calc11_card_722_eq : placed 1 (5, 7) card_12 = calc11_card_722 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_723_eq : placed 5 (5, 9) card_12 = calc11_card_723 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_724_eq : placed 3 (11, 7) card_12 = calc11_card_724 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_725_eq : placed 7 (11, 9) card_12 = calc11_card_725 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_726_eq : placed 0 (5, 1) card_490 = calc11_card_726 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_727_eq : placed 4 (11, 1) card_490 = calc11_card_727 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_728_eq : calc11_card_727.required ∪ ∅ = calc11_set_728 := by decide +kernel

theorem calc11_set_729_eq : calc11_card_727.envelope ∪ ∅ = calc11_set_729 := by decide +kernel

theorem calc11_set_730_eq : calc11_card_726.required ∪ calc11_set_728 = calc11_set_730 := by decide +kernel

theorem calc11_set_731_eq : calc11_card_726.envelope ∪ calc11_set_729 = calc11_set_731 := by decide +kernel

theorem calc11_set_732_eq : calc11_card_725.required ∪ calc11_set_730 = calc11_set_732 := by decide +kernel

theorem calc11_set_733_eq : calc11_card_725.envelope ∪ calc11_set_731 = calc11_set_733 := by decide +kernel

theorem calc11_set_734_eq : calc11_card_724.required ∪ calc11_set_732 = calc11_set_734 := by decide +kernel

theorem calc11_set_735_eq : calc11_card_724.envelope ∪ calc11_set_733 = calc11_set_735 := by decide +kernel

theorem calc11_set_736_eq : calc11_card_723.required ∪ calc11_set_734 = calc11_set_736 := by decide +kernel

theorem calc11_set_737_eq : calc11_card_723.envelope ∪ calc11_set_735 = calc11_set_737 := by decide +kernel

theorem calc11_set_738_eq : calc11_card_722.required ∪ calc11_set_736 = calc11_set_738 := by decide +kernel

theorem calc11_set_739_eq : calc11_card_722.envelope ∪ calc11_set_737 = calc11_set_739 := by decide +kernel

theorem calc11_set_740_eq : calc11_card_727.envelope ∩ calc11_card_722.envelope = calc11_set_740 := by decide +kernel

theorem calc11_set_741_eq : calc11_card_726.envelope ∩ calc11_set_740 = calc11_set_741 := by decide +kernel

theorem calc11_set_742_eq : calc11_card_725.envelope ∩ calc11_set_741 = calc11_set_742 := by decide +kernel

theorem calc11_set_743_eq : calc11_card_724.envelope ∩ calc11_set_742 = calc11_set_743 := by decide +kernel

theorem calc11_set_744_eq : calc11_card_723.envelope ∩ calc11_set_743 = calc11_set_744 := by decide +kernel

theorem calc11_set_745_eq : calc11_set_738 ∪ calc11_set_744 = calc11_set_745 := by decide +kernel

theorem calc11_finishA_746 : calc11_set_745.erase (9, 8) = inline_831.required := by decide +kernel

theorem calc11_finishT_746 : insert (9, 8) calc11_set_739 = inline_831.envelope := by decide +kernel

theorem eq_inline_831 : inline_831 = combine (9, 8) [placed 1 (5, 7) card_12, placed 5 (5, 9) card_12, placed 3 (11, 7) card_12, placed 7 (11, 9) card_12, placed 0 (5, 1) card_490, placed 4 (11, 1) card_490] := by
  rw [calc11_card_722_eq, calc11_card_723_eq, calc11_card_724_eq, calc11_card_725_eq, calc11_card_726_eq, calc11_card_727_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_728_eq, calc11_set_730_eq, calc11_set_732_eq, calc11_set_734_eq, calc11_set_736_eq, calc11_set_738_eq, calc11_set_740_eq, calc11_set_741_eq, calc11_set_742_eq, calc11_set_743_eq, calc11_set_744_eq, calc11_set_745_eq, calc11_finishA_746]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_729_eq, calc11_set_731_eq, calc11_set_733_eq, calc11_set_735_eq, calc11_set_737_eq, calc11_set_739_eq, calc11_finishT_746]
  · decide +kernel

theorem valid_inline_831 : Valid inline_831 := by
  rw [eq_inline_831]
  apply combination_rule (9, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 7) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 9) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 3 (11, 7) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 7 (11, 9) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 1) valid_490
  subst c
  exact placed_valid 4 (11, 1) valid_490

theorem calc11_card_747_eq : placed 3 (12, 7) card_459 = calc11_card_747 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_748_eq : placed 3 (11, 6) card_475 = calc11_card_748 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_749_eq : placed 5 (4, 10) card_587 = calc11_card_749 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_750_eq : placed 1 (4, 7) card_603 = calc11_card_750 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_751_eq : placed 0 (5, 5) card_605 = calc11_card_751 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_752_eq : placed 6 (11, 13) card_650 = calc11_card_752 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_753_eq : placed 0 (1, 1) card_684 = calc11_card_753 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_754_eq : placed 7 (13, 13) card_694 = calc11_card_754 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_755_eq : placed 0 (5, 3) card_695 = calc11_card_755 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_756_eq : placed 3 (13, 3) card_696 = calc11_card_756 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_757_eq : placed 1 (3, 4) card_698 = calc11_card_757 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_758_eq : placed 4 (13, 1) card_701 = calc11_card_758 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_759_eq : placed 4 (12, 3) card_707 = calc11_card_759 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_760_eq : calc11_card_759.required ∪ ∅ = calc11_set_760 := by decide +kernel

theorem calc11_set_761_eq : calc11_card_759.envelope ∪ ∅ = calc11_set_761 := by decide +kernel

theorem calc11_set_762_eq : inline_831.required ∪ calc11_set_760 = calc11_set_762 := by decide +kernel

theorem calc11_set_763_eq : inline_831.envelope ∪ calc11_set_761 = calc11_set_763 := by decide +kernel

theorem calc11_set_764_eq : calc11_card_758.required ∪ calc11_set_762 = calc11_set_764 := by decide +kernel

theorem calc11_set_765_eq : calc11_card_758.envelope ∪ calc11_set_763 = calc11_set_765 := by decide +kernel

theorem calc11_set_766_eq : calc11_card_757.required ∪ calc11_set_764 = calc11_set_766 := by decide +kernel

theorem calc11_set_767_eq : calc11_card_757.envelope ∪ calc11_set_765 = calc11_set_767 := by decide +kernel

theorem calc11_set_768_eq : calc11_card_756.required ∪ calc11_set_766 = calc11_set_768 := by decide +kernel

theorem calc11_set_769_eq : calc11_card_756.envelope ∪ calc11_set_767 = calc11_set_769 := by decide +kernel

theorem calc11_set_770_eq : calc11_card_755.required ∪ calc11_set_768 = calc11_set_770 := by decide +kernel

theorem calc11_set_771_eq : calc11_card_755.envelope ∪ calc11_set_769 = calc11_set_771 := by decide +kernel

theorem calc11_set_772_eq : calc11_card_754.required ∪ calc11_set_770 = calc11_set_772 := by decide +kernel

theorem calc11_set_773_eq : calc11_card_754.envelope ∪ calc11_set_771 = calc11_set_773 := by decide +kernel

theorem calc11_set_774_eq : inline_830.required ∪ calc11_set_772 = calc11_set_774 := by decide +kernel

theorem calc11_set_775_eq : inline_830.envelope ∪ calc11_set_773 = calc11_set_775 := by decide +kernel

theorem calc11_set_776_eq : inline_829.required ∪ calc11_set_774 = calc11_set_776 := by decide +kernel

theorem calc11_set_777_eq : inline_829.envelope ∪ calc11_set_775 = calc11_set_777 := by decide +kernel

theorem calc11_set_778_eq : calc11_card_753.required ∪ calc11_set_776 = calc11_set_778 := by decide +kernel

theorem calc11_set_779_eq : calc11_card_753.envelope ∪ calc11_set_777 = calc11_set_779 := by decide +kernel

theorem calc11_set_780_eq : calc11_card_752.required ∪ calc11_set_778 = calc11_set_780 := by decide +kernel

theorem calc11_set_781_eq : calc11_card_752.envelope ∪ calc11_set_779 = calc11_set_781 := by decide +kernel

theorem calc11_set_782_eq : calc11_card_751.required ∪ calc11_set_780 = calc11_set_782 := by decide +kernel

theorem calc11_set_783_eq : calc11_card_751.envelope ∪ calc11_set_781 = calc11_set_783 := by decide +kernel

theorem calc11_set_784_eq : calc11_card_750.required ∪ calc11_set_782 = calc11_set_784 := by decide +kernel

theorem calc11_set_785_eq : calc11_card_750.envelope ∪ calc11_set_783 = calc11_set_785 := by decide +kernel

theorem calc11_set_786_eq : calc11_card_749.required ∪ calc11_set_784 = calc11_set_786 := by decide +kernel

theorem calc11_set_787_eq : calc11_card_749.envelope ∪ calc11_set_785 = calc11_set_787 := by decide +kernel

theorem calc11_set_788_eq : calc11_card_748.required ∪ calc11_set_786 = calc11_set_788 := by decide +kernel

theorem calc11_set_789_eq : calc11_card_748.envelope ∪ calc11_set_787 = calc11_set_789 := by decide +kernel

theorem calc11_set_790_eq : calc11_card_747.required ∪ calc11_set_788 = calc11_set_790 := by decide +kernel

theorem calc11_set_791_eq : calc11_card_747.envelope ∪ calc11_set_789 = calc11_set_791 := by decide +kernel

theorem calc11_set_792_eq : calc11_card_759.envelope ∩ calc11_card_747.envelope = calc11_set_792 := by decide +kernel

theorem calc11_set_793_eq : inline_831.envelope ∩ calc11_set_792 = calc11_set_793 := by decide +kernel

theorem calc11_set_794_eq : calc11_card_758.envelope ∩ calc11_set_793 = calc11_set_794 := by decide +kernel

theorem calc11_set_795_eq : calc11_card_757.envelope ∩ calc11_set_794 = calc11_set_795 := by decide +kernel

theorem calc11_set_796_eq : calc11_card_756.envelope ∩ calc11_set_795 = calc11_set_796 := by decide +kernel

theorem calc11_set_797_eq : calc11_card_755.envelope ∩ calc11_set_796 = calc11_set_797 := by decide +kernel

theorem calc11_set_798_eq : calc11_card_754.envelope ∩ calc11_set_797 = calc11_set_798 := by decide +kernel

theorem calc11_set_799_eq : inline_830.envelope ∩ calc11_set_798 = calc11_set_799 := by decide +kernel

theorem calc11_set_800_eq : inline_829.envelope ∩ calc11_set_799 = calc11_set_800 := by decide +kernel

theorem calc11_set_801_eq : calc11_card_753.envelope ∩ calc11_set_800 = calc11_set_801 := by decide +kernel

theorem calc11_set_802_eq : calc11_card_752.envelope ∩ calc11_set_801 = calc11_set_802 := by decide +kernel

theorem calc11_set_803_eq : calc11_card_751.envelope ∩ calc11_set_802 = calc11_set_803 := by decide +kernel

theorem calc11_set_804_eq : calc11_card_750.envelope ∩ calc11_set_803 = calc11_set_804 := by decide +kernel

theorem calc11_set_805_eq : calc11_card_749.envelope ∩ calc11_set_804 = calc11_set_805 := by decide +kernel

theorem calc11_set_806_eq : calc11_card_748.envelope ∩ calc11_set_805 = calc11_set_806 := by decide +kernel

theorem calc11_set_807_eq : calc11_set_790 ∪ calc11_set_806 = calc11_set_807 := by decide +kernel

theorem calc11_finishA_808 : calc11_set_807.erase (7, 8) = card_708.required := by decide +kernel

theorem calc11_finishT_808 : insert (7, 8) calc11_set_791 = card_708.envelope := by decide +kernel

theorem eq_card_708 : card_708 = combine (7, 8) [placed 3 (12, 7) card_459, placed 3 (11, 6) card_475, placed 5 (4, 10) card_587, placed 1 (4, 7) card_603, placed 0 (5, 5) card_605, placed 6 (11, 13) card_650, placed 0 (1, 1) card_684, inline_829, inline_830, placed 7 (13, 13) card_694, placed 0 (5, 3) card_695, placed 3 (13, 3) card_696, placed 1 (3, 4) card_698, placed 4 (13, 1) card_701, inline_831, placed 4 (12, 3) card_707] := by
  rw [calc11_card_747_eq, calc11_card_748_eq, calc11_card_749_eq, calc11_card_750_eq, calc11_card_751_eq, calc11_card_752_eq, calc11_card_753_eq, calc11_card_754_eq, calc11_card_755_eq, calc11_card_756_eq, calc11_card_757_eq, calc11_card_758_eq, calc11_card_759_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_760_eq, calc11_set_762_eq, calc11_set_764_eq, calc11_set_766_eq, calc11_set_768_eq, calc11_set_770_eq, calc11_set_772_eq, calc11_set_774_eq, calc11_set_776_eq, calc11_set_778_eq, calc11_set_780_eq, calc11_set_782_eq, calc11_set_784_eq, calc11_set_786_eq, calc11_set_788_eq, calc11_set_790_eq, calc11_set_792_eq, calc11_set_793_eq, calc11_set_794_eq, calc11_set_795_eq, calc11_set_796_eq, calc11_set_797_eq, calc11_set_798_eq, calc11_set_799_eq, calc11_set_800_eq, calc11_set_801_eq, calc11_set_802_eq, calc11_set_803_eq, calc11_set_804_eq, calc11_set_805_eq, calc11_set_806_eq, calc11_set_807_eq, calc11_finishA_808]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_761_eq, calc11_set_763_eq, calc11_set_765_eq, calc11_set_767_eq, calc11_set_769_eq, calc11_set_771_eq, calc11_set_773_eq, calc11_set_775_eq, calc11_set_777_eq, calc11_set_779_eq, calc11_set_781_eq, calc11_set_783_eq, calc11_set_785_eq, calc11_set_787_eq, calc11_set_789_eq, calc11_set_791_eq, calc11_finishT_808]
  · decide +kernel

theorem valid_708 : Valid card_708 := by
  rw [eq_card_708]
  apply combination_rule (7, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (12, 7) valid_459
  rcases hc with rfl | hc
  · exact placed_valid 3 (11, 6) valid_475
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 10) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 7) valid_603
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 5) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 6 (11, 13) valid_650
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_684
  rcases hc with rfl | hc
  · exact valid_inline_829
  rcases hc with rfl | hc
  · exact valid_inline_830
  rcases hc with rfl | hc
  · exact placed_valid 7 (13, 13) valid_694
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_695
  rcases hc with rfl | hc
  · exact placed_valid 3 (13, 3) valid_696
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_698
  rcases hc with rfl | hc
  · exact placed_valid 4 (13, 1) valid_701
  rcases hc with rfl | hc
  · exact valid_inline_831
  subst c
  exact placed_valid 4 (12, 3) valid_707

theorem calc11_card_809_eq : placed 1 (2, 5) card_53 = calc11_card_809 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_810_eq : placed 5 (2, 7) card_56 = calc11_card_810 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_811_eq : placed 0 (4, 3) card_392 = calc11_card_811 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_812_eq : calc11_card_811.required ∪ ∅ = calc11_set_812 := by decide +kernel

theorem calc11_set_813_eq : calc11_card_811.envelope ∪ ∅ = calc11_set_813 := by decide +kernel

theorem calc11_set_814_eq : calc11_card_810.required ∪ calc11_set_812 = calc11_set_814 := by decide +kernel

theorem calc11_set_815_eq : calc11_card_810.envelope ∪ calc11_set_813 = calc11_set_815 := by decide +kernel

theorem calc11_set_816_eq : calc11_card_809.required ∪ calc11_set_814 = calc11_set_816 := by decide +kernel

theorem calc11_set_817_eq : calc11_card_809.envelope ∪ calc11_set_815 = calc11_set_817 := by decide +kernel

theorem calc11_set_818_eq : calc11_card_811.envelope ∩ calc11_card_809.envelope = calc11_set_818 := by decide +kernel

theorem calc11_set_819_eq : calc11_card_810.envelope ∩ calc11_set_818 = calc11_set_819 := by decide +kernel

theorem calc11_set_820_eq : calc11_set_816 ∪ calc11_set_819 = calc11_set_820 := by decide +kernel

theorem calc11_finishA_821 : calc11_set_820.erase (4, 5) = inline_832.required := by decide +kernel

theorem calc11_finishT_821 : insert (4, 5) calc11_set_817 = inline_832.envelope := by decide +kernel

theorem eq_inline_832 : inline_832 = combine (4, 5) [placed 1 (2, 5) card_53, placed 5 (2, 7) card_56, placed 0 (4, 3) card_392] := by
  rw [calc11_card_809_eq, calc11_card_810_eq, calc11_card_811_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_812_eq, calc11_set_814_eq, calc11_set_816_eq, calc11_set_818_eq, calc11_set_819_eq, calc11_set_820_eq, calc11_finishA_821]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_813_eq, calc11_set_815_eq, calc11_set_817_eq, calc11_finishT_821]
  · decide +kernel

theorem valid_inline_832 : Valid inline_832 := by
  rw [eq_inline_832]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_56
  subst c
  exact placed_valid 0 (4, 3) valid_392

theorem calc11_card_822_eq : placed 2 (5, 8) card_11 = calc11_card_822 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_823_eq : placed 7 (8, 7) card_253 = calc11_card_823 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_824_eq : inline_832.required ∪ ∅ = calc11_set_824 := by decide +kernel

theorem calc11_set_825_eq : inline_832.envelope ∪ ∅ = calc11_set_825 := by decide +kernel

theorem calc11_set_826_eq : calc11_card_823.required ∪ calc11_set_824 = calc11_set_826 := by decide +kernel

theorem calc11_set_827_eq : calc11_card_823.envelope ∪ calc11_set_825 = calc11_set_827 := by decide +kernel

theorem calc11_set_828_eq : calc11_card_822.required ∪ calc11_set_826 = calc11_set_828 := by decide +kernel

theorem calc11_set_829_eq : calc11_card_822.envelope ∪ calc11_set_827 = calc11_set_829 := by decide +kernel

theorem calc11_set_830_eq : inline_832.envelope ∩ calc11_card_822.envelope = calc11_set_830 := by decide +kernel

theorem calc11_set_831_eq : calc11_card_823.envelope ∩ calc11_set_830 = calc11_set_831 := by decide +kernel

theorem calc11_set_832_eq : calc11_set_828 ∪ calc11_set_831 = calc11_set_832 := by decide +kernel

theorem calc11_finishA_833 : calc11_set_832.erase (5, 4) = inline_833.required := by decide +kernel

theorem calc11_finishT_833 : insert (5, 4) calc11_set_829 = inline_833.envelope := by decide +kernel

theorem eq_inline_833 : inline_833 = combine (5, 4) [placed 2 (5, 8) card_11, placed 7 (8, 7) card_253, inline_832] := by
  rw [calc11_card_822_eq, calc11_card_823_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_824_eq, calc11_set_826_eq, calc11_set_828_eq, calc11_set_830_eq, calc11_set_831_eq, calc11_set_832_eq, calc11_finishA_833]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_825_eq, calc11_set_827_eq, calc11_set_829_eq, calc11_finishT_833]
  · decide +kernel

theorem valid_inline_833 : Valid inline_833 := by
  rw [eq_inline_833]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 8) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 7) valid_253
  subst c
  exact valid_inline_832

theorem calc11_card_834_eq : placed 2 (5, 7) card_6 = calc11_card_834 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_835_eq : placed 6 (6, 6) card_89 = calc11_card_835 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_836_eq : calc11_card_835.required ∪ ∅ = calc11_set_836 := by decide +kernel

theorem calc11_set_837_eq : calc11_card_835.envelope ∪ ∅ = calc11_set_837 := by decide +kernel

theorem calc11_set_838_eq : calc11_card_834.required ∪ calc11_set_836 = calc11_set_838 := by decide +kernel

theorem calc11_set_839_eq : calc11_card_834.envelope ∪ calc11_set_837 = calc11_set_839 := by decide +kernel

theorem calc11_set_840_eq : calc11_card_835.envelope ∩ calc11_card_834.envelope = calc11_set_840 := by decide +kernel

theorem calc11_set_841_eq : calc11_set_838 ∪ calc11_set_840 = calc11_set_841 := by decide +kernel

theorem calc11_finishA_842 : calc11_set_841.erase (5, 3) = inline_834.required := by decide +kernel

theorem calc11_finishT_842 : insert (5, 3) calc11_set_839 = inline_834.envelope := by decide +kernel

theorem eq_inline_834 : inline_834 = combine (5, 3) [placed 2 (5, 7) card_6, placed 6 (6, 6) card_89] := by
  rw [calc11_card_834_eq, calc11_card_835_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_836_eq, calc11_set_838_eq, calc11_set_840_eq, calc11_set_841_eq, calc11_finishA_842]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_837_eq, calc11_set_839_eq, calc11_finishT_842]
  · decide +kernel

theorem valid_inline_834 : Valid inline_834 := by
  rw [eq_inline_834]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 7) valid_6
  subst c
  exact placed_valid 6 (6, 6) valid_89

theorem calc11_card_843_eq : placed 2 (5, 8) card_11 = calc11_card_843 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_844_eq : placed 2 (4, 8) card_521 = calc11_card_844 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_845_eq : inline_834.required ∪ ∅ = calc11_set_845 := by decide +kernel

theorem calc11_set_846_eq : inline_834.envelope ∪ ∅ = calc11_set_846 := by decide +kernel

theorem calc11_set_847_eq : calc11_card_844.required ∪ calc11_set_845 = calc11_set_847 := by decide +kernel

theorem calc11_set_848_eq : calc11_card_844.envelope ∪ calc11_set_846 = calc11_set_848 := by decide +kernel

theorem calc11_set_849_eq : calc11_card_843.required ∪ calc11_set_847 = calc11_set_849 := by decide +kernel

theorem calc11_set_850_eq : calc11_card_843.envelope ∪ calc11_set_848 = calc11_set_850 := by decide +kernel

theorem calc11_set_851_eq : inline_834.envelope ∩ calc11_card_843.envelope = calc11_set_851 := by decide +kernel

theorem calc11_set_852_eq : calc11_card_844.envelope ∩ calc11_set_851 = calc11_set_852 := by decide +kernel

theorem calc11_set_853_eq : calc11_set_849 ∪ calc11_set_852 = calc11_set_853 := by decide +kernel

theorem calc11_finishA_854 : calc11_set_853.erase (5, 4) = inline_835.required := by decide +kernel

theorem calc11_finishT_854 : insert (5, 4) calc11_set_850 = inline_835.envelope := by decide +kernel

theorem eq_inline_835 : inline_835 = combine (5, 4) [placed 2 (5, 8) card_11, placed 2 (4, 8) card_521, inline_834] := by
  rw [calc11_card_843_eq, calc11_card_844_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_845_eq, calc11_set_847_eq, calc11_set_849_eq, calc11_set_851_eq, calc11_set_852_eq, calc11_set_853_eq, calc11_finishA_854]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_846_eq, calc11_set_848_eq, calc11_set_850_eq, calc11_finishT_854]
  · decide +kernel

theorem valid_inline_835 : Valid inline_835 := by
  rw [eq_inline_835]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 8) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_521
  subst c
  exact valid_inline_834

theorem calc11_card_855_eq : placed 3 (9, 3) card_524 = calc11_card_855 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_856_eq : placed 7 (9, 9) card_536 = calc11_card_856 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_857_eq : placed 7 (10, 7) card_545 = calc11_card_857 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_858_eq : placed 3 (10, 3) card_655 = calc11_card_858 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_859_eq : placed 2 (1, 11) card_664 = calc11_card_859 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_860_eq : inline_835.required ∪ ∅ = calc11_set_860 := by decide +kernel

theorem calc11_set_861_eq : inline_835.envelope ∪ ∅ = calc11_set_861 := by decide +kernel

theorem calc11_set_862_eq : inline_833.required ∪ calc11_set_860 = calc11_set_862 := by decide +kernel

theorem calc11_set_863_eq : inline_833.envelope ∪ calc11_set_861 = calc11_set_863 := by decide +kernel

theorem calc11_set_864_eq : calc11_card_859.required ∪ calc11_set_862 = calc11_set_864 := by decide +kernel

theorem calc11_set_865_eq : calc11_card_859.envelope ∪ calc11_set_863 = calc11_set_865 := by decide +kernel

theorem calc11_set_866_eq : calc11_card_858.required ∪ calc11_set_864 = calc11_set_866 := by decide +kernel

theorem calc11_set_867_eq : calc11_card_858.envelope ∪ calc11_set_865 = calc11_set_867 := by decide +kernel

theorem calc11_set_868_eq : calc11_card_857.required ∪ calc11_set_866 = calc11_set_868 := by decide +kernel

theorem calc11_set_869_eq : calc11_card_857.envelope ∪ calc11_set_867 = calc11_set_869 := by decide +kernel

theorem calc11_set_870_eq : calc11_card_856.required ∪ calc11_set_868 = calc11_set_870 := by decide +kernel

theorem calc11_set_871_eq : calc11_card_856.envelope ∪ calc11_set_869 = calc11_set_871 := by decide +kernel

theorem calc11_set_872_eq : calc11_card_855.required ∪ calc11_set_870 = calc11_set_872 := by decide +kernel

theorem calc11_set_873_eq : calc11_card_855.envelope ∪ calc11_set_871 = calc11_set_873 := by decide +kernel

theorem calc11_set_874_eq : inline_835.envelope ∩ calc11_card_855.envelope = calc11_set_874 := by decide +kernel

theorem calc11_set_875_eq : inline_833.envelope ∩ calc11_set_874 = calc11_set_875 := by decide +kernel

theorem calc11_set_876_eq : calc11_card_859.envelope ∩ calc11_set_875 = calc11_set_876 := by decide +kernel

theorem calc11_set_877_eq : calc11_card_858.envelope ∩ calc11_set_876 = calc11_set_877 := by decide +kernel

theorem calc11_set_878_eq : calc11_card_857.envelope ∩ calc11_set_877 = calc11_set_878 := by decide +kernel

theorem calc11_set_879_eq : calc11_card_856.envelope ∩ calc11_set_878 = calc11_set_879 := by decide +kernel

theorem calc11_set_880_eq : calc11_set_872 ∪ calc11_set_879 = calc11_set_880 := by decide +kernel

theorem calc11_finishA_881 : calc11_set_880.erase (6, 6) = inline_836.required := by decide +kernel

theorem calc11_finishT_881 : insert (6, 6) calc11_set_873 = inline_836.envelope := by decide +kernel

theorem eq_inline_836 : inline_836 = combine (6, 6) [placed 3 (9, 3) card_524, placed 7 (9, 9) card_536, placed 7 (10, 7) card_545, placed 3 (10, 3) card_655, placed 2 (1, 11) card_664, inline_833, inline_835] := by
  rw [calc11_card_855_eq, calc11_card_856_eq, calc11_card_857_eq, calc11_card_858_eq, calc11_card_859_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_860_eq, calc11_set_862_eq, calc11_set_864_eq, calc11_set_866_eq, calc11_set_868_eq, calc11_set_870_eq, calc11_set_872_eq, calc11_set_874_eq, calc11_set_875_eq, calc11_set_876_eq, calc11_set_877_eq, calc11_set_878_eq, calc11_set_879_eq, calc11_set_880_eq, calc11_finishA_881]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_861_eq, calc11_set_863_eq, calc11_set_865_eq, calc11_set_867_eq, calc11_set_869_eq, calc11_set_871_eq, calc11_set_873_eq, calc11_finishT_881]
  · decide +kernel

theorem valid_inline_836 : Valid inline_836 := by
  rw [eq_inline_836]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 3) valid_524
  rcases hc with rfl | hc
  · exact placed_valid 7 (9, 9) valid_536
  rcases hc with rfl | hc
  · exact placed_valid 7 (10, 7) valid_545
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 3) valid_655
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 11) valid_664
  rcases hc with rfl | hc
  · exact valid_inline_833
  subst c
  exact valid_inline_835

theorem calc11_card_882_eq : placed 4 (6, 3) card_14 = calc11_card_882 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_883_eq : placed 3 (8, 4) card_116 = calc11_card_883 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_884_eq : placed 3 (7, 4) card_181 = calc11_card_884 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_885_eq : inline_836.required ∪ ∅ = calc11_set_885 := by decide +kernel

theorem calc11_set_886_eq : inline_836.envelope ∪ ∅ = calc11_set_886 := by decide +kernel

theorem calc11_set_887_eq : calc11_card_884.required ∪ calc11_set_885 = calc11_set_887 := by decide +kernel

theorem calc11_set_888_eq : calc11_card_884.envelope ∪ calc11_set_886 = calc11_set_888 := by decide +kernel

theorem calc11_set_889_eq : calc11_card_883.required ∪ calc11_set_887 = calc11_set_889 := by decide +kernel

theorem calc11_set_890_eq : calc11_card_883.envelope ∪ calc11_set_888 = calc11_set_890 := by decide +kernel

theorem calc11_set_891_eq : calc11_card_882.required ∪ calc11_set_889 = calc11_set_891 := by decide +kernel

theorem calc11_set_892_eq : calc11_card_882.envelope ∪ calc11_set_890 = calc11_set_892 := by decide +kernel

theorem calc11_set_893_eq : inline_836.envelope ∩ calc11_card_882.envelope = calc11_set_893 := by decide +kernel

theorem calc11_set_894_eq : calc11_card_884.envelope ∩ calc11_set_893 = calc11_set_894 := by decide +kernel

theorem calc11_set_895_eq : calc11_card_883.envelope ∩ calc11_set_894 = calc11_set_895 := by decide +kernel

theorem calc11_set_896_eq : calc11_set_891 ∪ calc11_set_895 = calc11_set_896 := by decide +kernel

theorem calc11_finishA_897 : calc11_set_896.erase (5, 7) = card_709.required := by decide +kernel

theorem calc11_finishT_897 : insert (5, 7) calc11_set_892 = card_709.envelope := by decide +kernel

theorem eq_card_709 : card_709 = combine (5, 7) [placed 4 (6, 3) card_14, placed 3 (8, 4) card_116, placed 3 (7, 4) card_181, inline_836] := by
  rw [calc11_card_882_eq, calc11_card_883_eq, calc11_card_884_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_885_eq, calc11_set_887_eq, calc11_set_889_eq, calc11_set_891_eq, calc11_set_893_eq, calc11_set_894_eq, calc11_set_895_eq, calc11_set_896_eq, calc11_finishA_897]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_886_eq, calc11_set_888_eq, calc11_set_890_eq, calc11_set_892_eq, calc11_finishT_897]
  · decide +kernel

theorem valid_709 : Valid card_709 := by
  rw [eq_card_709]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_181
  subst c
  exact valid_inline_836

theorem calc11_card_898_eq : placed 0 (3, 2) card_6 = calc11_card_898 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_899_eq : placed 5 (2, 6) card_196 = calc11_card_899 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_900_eq : calc11_card_899.required ∪ ∅ = calc11_set_900 := by decide +kernel

theorem calc11_set_901_eq : calc11_card_899.envelope ∪ ∅ = calc11_set_901 := by decide +kernel

theorem calc11_set_902_eq : calc11_card_898.required ∪ calc11_set_900 = calc11_set_902 := by decide +kernel

theorem calc11_set_903_eq : calc11_card_898.envelope ∪ calc11_set_901 = calc11_set_903 := by decide +kernel

theorem calc11_set_904_eq : calc11_card_899.envelope ∩ calc11_card_898.envelope = calc11_set_904 := by decide +kernel

theorem calc11_set_905_eq : calc11_set_902 ∪ calc11_set_904 = calc11_set_905 := by decide +kernel

theorem calc11_finishA_906 : calc11_set_905.erase (3, 2) = inline_837.required := by decide +kernel

theorem calc11_finishT_906 : insert (3, 2) calc11_set_903 = inline_837.envelope := by decide +kernel

theorem eq_inline_837 : inline_837 = combine (3, 2) [placed 0 (3, 2) card_6, placed 5 (2, 6) card_196] := by
  rw [calc11_card_898_eq, calc11_card_899_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_900_eq, calc11_set_902_eq, calc11_set_904_eq, calc11_set_905_eq, calc11_finishA_906]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_901_eq, calc11_set_903_eq, calc11_finishT_906]
  · decide +kernel

theorem valid_inline_837 : Valid inline_837 := by
  rw [eq_inline_837]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_6
  subst c
  exact placed_valid 5 (2, 6) valid_196

theorem calc11_card_907_eq : placed 2 (3, 7) card_7 = calc11_card_907 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_908_eq : placed 5 (0, 6) card_115 = calc11_card_908 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_909_eq : placed 1 (1, 2) card_577 = calc11_card_909 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_910_eq : calc11_card_909.required ∪ ∅ = calc11_set_910 := by decide +kernel

theorem calc11_set_911_eq : calc11_card_909.envelope ∪ ∅ = calc11_set_911 := by decide +kernel

theorem calc11_set_912_eq : inline_837.required ∪ calc11_set_910 = calc11_set_912 := by decide +kernel

theorem calc11_set_913_eq : inline_837.envelope ∪ calc11_set_911 = calc11_set_913 := by decide +kernel

theorem calc11_set_914_eq : calc11_card_908.required ∪ calc11_set_912 = calc11_set_914 := by decide +kernel

theorem calc11_set_915_eq : calc11_card_908.envelope ∪ calc11_set_913 = calc11_set_915 := by decide +kernel

theorem calc11_set_916_eq : calc11_card_907.required ∪ calc11_set_914 = calc11_set_916 := by decide +kernel

theorem calc11_set_917_eq : calc11_card_907.envelope ∪ calc11_set_915 = calc11_set_917 := by decide +kernel

theorem calc11_set_918_eq : calc11_card_909.envelope ∩ calc11_card_907.envelope = calc11_set_918 := by decide +kernel

theorem calc11_set_919_eq : inline_837.envelope ∩ calc11_set_918 = calc11_set_919 := by decide +kernel

theorem calc11_set_920_eq : calc11_card_908.envelope ∩ calc11_set_919 = calc11_set_920 := by decide +kernel

theorem calc11_set_921_eq : calc11_set_916 ∪ calc11_set_920 = calc11_set_921 := by decide +kernel

theorem calc11_finishA_922 : calc11_set_921.erase (3, 3) = inline_838.required := by decide +kernel

theorem calc11_finishT_922 : insert (3, 3) calc11_set_917 = inline_838.envelope := by decide +kernel

theorem eq_inline_838 : inline_838 = combine (3, 3) [placed 2 (3, 7) card_7, placed 5 (0, 6) card_115, inline_837, placed 1 (1, 2) card_577] := by
  rw [calc11_card_907_eq, calc11_card_908_eq, calc11_card_909_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_910_eq, calc11_set_912_eq, calc11_set_914_eq, calc11_set_916_eq, calc11_set_918_eq, calc11_set_919_eq, calc11_set_920_eq, calc11_set_921_eq, calc11_finishA_922]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_911_eq, calc11_set_913_eq, calc11_set_915_eq, calc11_set_917_eq, calc11_finishT_922]
  · decide +kernel

theorem valid_inline_838 : Valid inline_838 := by
  rw [eq_inline_838]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_115
  rcases hc with rfl | hc
  · exact valid_inline_837
  subst c
  exact placed_valid 1 (1, 2) valid_577

theorem calc11_card_923_eq : placed 0 (2, 2) card_13 = calc11_card_923 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_924_eq : placed 4 (4, 2) card_14 = calc11_card_924 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_925_eq : placed 1 (0, 3) card_117 = calc11_card_925 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_926_eq : inline_838.required ∪ ∅ = calc11_set_926 := by decide +kernel

theorem calc11_set_927_eq : inline_838.envelope ∪ ∅ = calc11_set_927 := by decide +kernel

theorem calc11_set_928_eq : calc11_card_925.required ∪ calc11_set_926 = calc11_set_928 := by decide +kernel

theorem calc11_set_929_eq : calc11_card_925.envelope ∪ calc11_set_927 = calc11_set_929 := by decide +kernel

theorem calc11_set_930_eq : calc11_card_924.required ∪ calc11_set_928 = calc11_set_930 := by decide +kernel

theorem calc11_set_931_eq : calc11_card_924.envelope ∪ calc11_set_929 = calc11_set_931 := by decide +kernel

theorem calc11_set_932_eq : calc11_card_923.required ∪ calc11_set_930 = calc11_set_932 := by decide +kernel

theorem calc11_set_933_eq : calc11_card_923.envelope ∪ calc11_set_931 = calc11_set_933 := by decide +kernel

theorem calc11_set_934_eq : inline_838.envelope ∩ calc11_card_923.envelope = calc11_set_934 := by decide +kernel

theorem calc11_set_935_eq : calc11_card_925.envelope ∩ calc11_set_934 = calc11_set_935 := by decide +kernel

theorem calc11_set_936_eq : calc11_card_924.envelope ∩ calc11_set_935 = calc11_set_936 := by decide +kernel

theorem calc11_set_937_eq : calc11_set_932 ∪ calc11_set_936 = calc11_set_937 := by decide +kernel

theorem calc11_finishA_938 : calc11_set_937.erase (3, 6) = card_710.required := by decide +kernel

theorem calc11_finishT_938 : insert (3, 6) calc11_set_933 = card_710.envelope := by decide +kernel

theorem eq_card_710 : card_710 = combine (3, 6) [placed 0 (2, 2) card_13, placed 4 (4, 2) card_14, placed 1 (0, 3) card_117, inline_838] := by
  rw [calc11_card_923_eq, calc11_card_924_eq, calc11_card_925_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_926_eq, calc11_set_928_eq, calc11_set_930_eq, calc11_set_932_eq, calc11_set_934_eq, calc11_set_935_eq, calc11_set_936_eq, calc11_set_937_eq, calc11_finishA_938]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_927_eq, calc11_set_929_eq, calc11_set_931_eq, calc11_set_933_eq, calc11_finishT_938]
  · decide +kernel

theorem valid_710 : Valid card_710 := by
  rw [eq_card_710]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_117
  subst c
  exact valid_inline_838

theorem calc11_card_939_eq : placed 5 (1, 6) card_104 = calc11_card_939 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_940_eq : placed 5 (1, 6) card_359 = calc11_card_940 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_941_eq : placed 2 (1, 9) card_452 = calc11_card_941 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_942_eq : placed 0 (3, 2) card_476 = calc11_card_942 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_943_eq : placed 2 (3, 9) card_479 = calc11_card_943 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_944_eq : placed 4 (9, 0) card_520 = calc11_card_944 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_945_eq : calc11_card_944.required ∪ ∅ = calc11_set_945 := by decide +kernel

theorem calc11_set_946_eq : calc11_card_944.envelope ∪ ∅ = calc11_set_946 := by decide +kernel

theorem calc11_set_947_eq : calc11_card_943.required ∪ calc11_set_945 = calc11_set_947 := by decide +kernel

theorem calc11_set_948_eq : calc11_card_943.envelope ∪ calc11_set_946 = calc11_set_948 := by decide +kernel

theorem calc11_set_949_eq : calc11_card_942.required ∪ calc11_set_947 = calc11_set_949 := by decide +kernel

theorem calc11_set_950_eq : calc11_card_942.envelope ∪ calc11_set_948 = calc11_set_950 := by decide +kernel

theorem calc11_set_951_eq : calc11_card_941.required ∪ calc11_set_949 = calc11_set_951 := by decide +kernel

theorem calc11_set_952_eq : calc11_card_941.envelope ∪ calc11_set_950 = calc11_set_952 := by decide +kernel

theorem calc11_set_953_eq : calc11_card_940.required ∪ calc11_set_951 = calc11_set_953 := by decide +kernel

theorem calc11_set_954_eq : calc11_card_940.envelope ∪ calc11_set_952 = calc11_set_954 := by decide +kernel

theorem calc11_set_955_eq : calc11_card_939.required ∪ calc11_set_953 = calc11_set_955 := by decide +kernel

theorem calc11_set_956_eq : calc11_card_939.envelope ∪ calc11_set_954 = calc11_set_956 := by decide +kernel

theorem calc11_set_957_eq : calc11_card_944.envelope ∩ calc11_card_939.envelope = calc11_set_957 := by decide +kernel

theorem calc11_set_958_eq : calc11_card_943.envelope ∩ calc11_set_957 = calc11_set_958 := by decide +kernel

theorem calc11_set_959_eq : calc11_card_942.envelope ∩ calc11_set_958 = calc11_set_959 := by decide +kernel

theorem calc11_set_960_eq : calc11_card_941.envelope ∩ calc11_set_959 = calc11_set_960 := by decide +kernel

theorem calc11_set_961_eq : calc11_card_940.envelope ∩ calc11_set_960 = calc11_set_961 := by decide +kernel

theorem calc11_set_962_eq : calc11_set_955 ∪ calc11_set_961 = calc11_set_962 := by decide +kernel

theorem calc11_finishA_963 : calc11_set_962.erase (6, 5) = inline_839.required := by decide +kernel

theorem calc11_finishT_963 : insert (6, 5) calc11_set_956 = inline_839.envelope := by decide +kernel

theorem eq_inline_839 : inline_839 = combine (6, 5) [placed 5 (1, 6) card_104, placed 5 (1, 6) card_359, placed 2 (1, 9) card_452, placed 0 (3, 2) card_476, placed 2 (3, 9) card_479, placed 4 (9, 0) card_520] := by
  rw [calc11_card_939_eq, calc11_card_940_eq, calc11_card_941_eq, calc11_card_942_eq, calc11_card_943_eq, calc11_card_944_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_945_eq, calc11_set_947_eq, calc11_set_949_eq, calc11_set_951_eq, calc11_set_953_eq, calc11_set_955_eq, calc11_set_957_eq, calc11_set_958_eq, calc11_set_959_eq, calc11_set_960_eq, calc11_set_961_eq, calc11_set_962_eq, calc11_finishA_963]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_946_eq, calc11_set_948_eq, calc11_set_950_eq, calc11_set_952_eq, calc11_set_954_eq, calc11_set_956_eq, calc11_finishT_963]
  · decide +kernel

theorem valid_inline_839 : Valid inline_839 := by
  rw [eq_inline_839]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_104
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_359
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 9) valid_452
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_476
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_479
  subst c
  exact placed_valid 4 (9, 0) valid_520

theorem calc11_card_964_eq : placed 4 (7, 3) card_120 = calc11_card_964 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_965_eq : placed 1 (1, 4) card_338 = calc11_card_965 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_966_eq : placed 1 (1, 3) card_437 = calc11_card_966 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_967_eq : placed 1 (0, 4) card_611 = calc11_card_967 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_968_eq : placed 5 (1, 7) card_613 = calc11_card_968 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_969_eq : placed 2 (1, 10) card_634 = calc11_card_969 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_970_eq : placed 2 (3, 10) card_642 = calc11_card_970 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_971_eq : placed 2 (3, 10) card_643 = calc11_card_971 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_972_eq : inline_839.required ∪ ∅ = calc11_set_972 := by decide +kernel

theorem calc11_set_973_eq : inline_839.envelope ∪ ∅ = calc11_set_973 := by decide +kernel

theorem calc11_set_974_eq : calc11_card_971.required ∪ calc11_set_972 = calc11_set_974 := by decide +kernel

theorem calc11_set_975_eq : calc11_card_971.envelope ∪ calc11_set_973 = calc11_set_975 := by decide +kernel

theorem calc11_set_976_eq : calc11_card_970.required ∪ calc11_set_974 = calc11_set_976 := by decide +kernel

theorem calc11_set_977_eq : calc11_card_970.envelope ∪ calc11_set_975 = calc11_set_977 := by decide +kernel

theorem calc11_set_978_eq : calc11_card_969.required ∪ calc11_set_976 = calc11_set_978 := by decide +kernel

theorem calc11_set_979_eq : calc11_card_969.envelope ∪ calc11_set_977 = calc11_set_979 := by decide +kernel

theorem calc11_set_980_eq : calc11_card_968.required ∪ calc11_set_978 = calc11_set_980 := by decide +kernel

theorem calc11_set_981_eq : calc11_card_968.envelope ∪ calc11_set_979 = calc11_set_981 := by decide +kernel

theorem calc11_set_982_eq : calc11_card_967.required ∪ calc11_set_980 = calc11_set_982 := by decide +kernel

theorem calc11_set_983_eq : calc11_card_967.envelope ∪ calc11_set_981 = calc11_set_983 := by decide +kernel

theorem calc11_set_984_eq : calc11_card_966.required ∪ calc11_set_982 = calc11_set_984 := by decide +kernel

theorem calc11_set_985_eq : calc11_card_966.envelope ∪ calc11_set_983 = calc11_set_985 := by decide +kernel

theorem calc11_set_986_eq : calc11_card_965.required ∪ calc11_set_984 = calc11_set_986 := by decide +kernel

theorem calc11_set_987_eq : calc11_card_965.envelope ∪ calc11_set_985 = calc11_set_987 := by decide +kernel

theorem calc11_set_988_eq : calc11_card_964.required ∪ calc11_set_986 = calc11_set_988 := by decide +kernel

theorem calc11_set_989_eq : calc11_card_964.envelope ∪ calc11_set_987 = calc11_set_989 := by decide +kernel

theorem calc11_set_990_eq : inline_839.envelope ∩ calc11_card_964.envelope = calc11_set_990 := by decide +kernel

theorem calc11_set_991_eq : calc11_card_971.envelope ∩ calc11_set_990 = calc11_set_991 := by decide +kernel

theorem calc11_set_992_eq : calc11_card_970.envelope ∩ calc11_set_991 = calc11_set_992 := by decide +kernel

theorem calc11_set_993_eq : calc11_card_969.envelope ∩ calc11_set_992 = calc11_set_993 := by decide +kernel

theorem calc11_set_994_eq : calc11_card_968.envelope ∩ calc11_set_993 = calc11_set_994 := by decide +kernel

theorem calc11_set_995_eq : calc11_card_967.envelope ∩ calc11_set_994 = calc11_set_995 := by decide +kernel

theorem calc11_set_996_eq : calc11_card_966.envelope ∩ calc11_set_995 = calc11_set_996 := by decide +kernel

theorem calc11_set_997_eq : calc11_card_965.envelope ∩ calc11_set_996 = calc11_set_997 := by decide +kernel

theorem calc11_set_998_eq : calc11_set_988 ∪ calc11_set_997 = calc11_set_998 := by decide +kernel

theorem calc11_finishA_999 : calc11_set_998.erase (6, 6) = card_711.required := by decide +kernel

theorem calc11_finishT_999 : insert (6, 6) calc11_set_989 = card_711.envelope := by decide +kernel

theorem eq_card_711 : card_711 = combine (6, 6) [placed 4 (7, 3) card_120, placed 1 (1, 4) card_338, placed 1 (1, 3) card_437, placed 1 (0, 4) card_611, placed 5 (1, 7) card_613, placed 2 (1, 10) card_634, placed 2 (3, 10) card_642, placed 2 (3, 10) card_643, inline_839] := by
  rw [calc11_card_964_eq, calc11_card_965_eq, calc11_card_966_eq, calc11_card_967_eq, calc11_card_968_eq, calc11_card_969_eq, calc11_card_970_eq, calc11_card_971_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_972_eq, calc11_set_974_eq, calc11_set_976_eq, calc11_set_978_eq, calc11_set_980_eq, calc11_set_982_eq, calc11_set_984_eq, calc11_set_986_eq, calc11_set_988_eq, calc11_set_990_eq, calc11_set_991_eq, calc11_set_992_eq, calc11_set_993_eq, calc11_set_994_eq, calc11_set_995_eq, calc11_set_996_eq, calc11_set_997_eq, calc11_set_998_eq, calc11_finishA_999]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_973_eq, calc11_set_975_eq, calc11_set_977_eq, calc11_set_979_eq, calc11_set_981_eq, calc11_set_983_eq, calc11_set_985_eq, calc11_set_987_eq, calc11_set_989_eq, calc11_finishT_999]
  · decide +kernel

theorem valid_711 : Valid card_711 := by
  rw [eq_card_711]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_120
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_338
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_437
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_611
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_613
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_634
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 10) valid_642
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 10) valid_643
  subst c
  exact valid_inline_839

theorem calc11_card_1000_eq : placed 2 (5, 7) card_44 = calc11_card_1000 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1001_eq : placed 3 (10, 3) card_545 = calc11_card_1001 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1002_eq : placed 7 (10, 7) card_655 = calc11_card_1002 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1003_eq : calc11_card_1002.required ∪ ∅ = calc11_set_1003 := by decide +kernel

theorem calc11_set_1004_eq : calc11_card_1002.envelope ∪ ∅ = calc11_set_1004 := by decide +kernel

theorem calc11_set_1005_eq : calc11_card_1001.required ∪ calc11_set_1003 = calc11_set_1005 := by decide +kernel

theorem calc11_set_1006_eq : calc11_card_1001.envelope ∪ calc11_set_1004 = calc11_set_1006 := by decide +kernel

theorem calc11_set_1007_eq : calc11_card_1000.required ∪ calc11_set_1005 = calc11_set_1007 := by decide +kernel

theorem calc11_set_1008_eq : calc11_card_1000.envelope ∪ calc11_set_1006 = calc11_set_1008 := by decide +kernel

theorem calc11_set_1009_eq : calc11_card_1002.envelope ∩ calc11_card_1000.envelope = calc11_set_1009 := by decide +kernel

theorem calc11_set_1010_eq : calc11_card_1001.envelope ∩ calc11_set_1009 = calc11_set_1010 := by decide +kernel

theorem calc11_set_1011_eq : calc11_set_1007 ∪ calc11_set_1010 = calc11_set_1011 := by decide +kernel

theorem calc11_finishA_1012 : calc11_set_1011.erase (6, 4) = inline_840.required := by decide +kernel

theorem calc11_finishT_1012 : insert (6, 4) calc11_set_1008 = inline_840.envelope := by decide +kernel

theorem eq_inline_840 : inline_840 = combine (6, 4) [placed 2 (5, 7) card_44, placed 3 (10, 3) card_545, placed 7 (10, 7) card_655] := by
  rw [calc11_card_1000_eq, calc11_card_1001_eq, calc11_card_1002_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1003_eq, calc11_set_1005_eq, calc11_set_1007_eq, calc11_set_1009_eq, calc11_set_1010_eq, calc11_set_1011_eq, calc11_finishA_1012]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1004_eq, calc11_set_1006_eq, calc11_set_1008_eq, calc11_finishT_1012]
  · decide +kernel

theorem valid_inline_840 : Valid inline_840 := by
  rw [eq_inline_840]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 7) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 3) valid_545
  subst c
  exact placed_valid 7 (10, 7) valid_655

theorem calc11_card_1013_eq : placed 5 (2, 7) card_116 = calc11_card_1013 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1014_eq : placed 5 (2, 8) card_297 = calc11_card_1014 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1015_eq : placed 3 (8, 3) card_435 = calc11_card_1015 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1016_eq : placed 1 (2, 3) card_435 = calc11_card_1016 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1017_eq : placed 7 (10, 8) card_649 = calc11_card_1017 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1018_eq : inline_840.required ∪ ∅ = calc11_set_1018 := by decide +kernel

theorem calc11_set_1019_eq : inline_840.envelope ∪ ∅ = calc11_set_1019 := by decide +kernel

theorem calc11_set_1020_eq : calc11_card_1017.required ∪ calc11_set_1018 = calc11_set_1020 := by decide +kernel

theorem calc11_set_1021_eq : calc11_card_1017.envelope ∪ calc11_set_1019 = calc11_set_1021 := by decide +kernel

theorem calc11_set_1022_eq : calc11_card_1016.required ∪ calc11_set_1020 = calc11_set_1022 := by decide +kernel

theorem calc11_set_1023_eq : calc11_card_1016.envelope ∪ calc11_set_1021 = calc11_set_1023 := by decide +kernel

theorem calc11_set_1024_eq : calc11_card_1015.required ∪ calc11_set_1022 = calc11_set_1024 := by decide +kernel

theorem calc11_set_1025_eq : calc11_card_1015.envelope ∪ calc11_set_1023 = calc11_set_1025 := by decide +kernel

theorem calc11_set_1026_eq : calc11_card_1014.required ∪ calc11_set_1024 = calc11_set_1026 := by decide +kernel

theorem calc11_set_1027_eq : calc11_card_1014.envelope ∪ calc11_set_1025 = calc11_set_1027 := by decide +kernel

theorem calc11_set_1028_eq : calc11_card_1013.required ∪ calc11_set_1026 = calc11_set_1028 := by decide +kernel

theorem calc11_set_1029_eq : calc11_card_1013.envelope ∪ calc11_set_1027 = calc11_set_1029 := by decide +kernel

theorem calc11_set_1030_eq : inline_840.envelope ∩ calc11_card_1013.envelope = calc11_set_1030 := by decide +kernel

theorem calc11_set_1031_eq : calc11_card_1017.envelope ∩ calc11_set_1030 = calc11_set_1031 := by decide +kernel

theorem calc11_set_1032_eq : calc11_card_1016.envelope ∩ calc11_set_1031 = calc11_set_1032 := by decide +kernel

theorem calc11_set_1033_eq : calc11_card_1015.envelope ∩ calc11_set_1032 = calc11_set_1033 := by decide +kernel

theorem calc11_set_1034_eq : calc11_card_1014.envelope ∩ calc11_set_1033 = calc11_set_1034 := by decide +kernel

theorem calc11_set_1035_eq : calc11_set_1028 ∪ calc11_set_1034 = calc11_set_1035 := by decide +kernel

theorem calc11_finishA_1036 : calc11_set_1035.erase (5, 4) = inline_841.required := by decide +kernel

theorem calc11_finishT_1036 : insert (5, 4) calc11_set_1029 = inline_841.envelope := by decide +kernel

theorem eq_inline_841 : inline_841 = combine (5, 4) [placed 5 (2, 7) card_116, placed 5 (2, 8) card_297, placed 3 (8, 3) card_435, placed 1 (2, 3) card_435, placed 7 (10, 8) card_649, inline_840] := by
  rw [calc11_card_1013_eq, calc11_card_1014_eq, calc11_card_1015_eq, calc11_card_1016_eq, calc11_card_1017_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1018_eq, calc11_set_1020_eq, calc11_set_1022_eq, calc11_set_1024_eq, calc11_set_1026_eq, calc11_set_1028_eq, calc11_set_1030_eq, calc11_set_1031_eq, calc11_set_1032_eq, calc11_set_1033_eq, calc11_set_1034_eq, calc11_set_1035_eq, calc11_finishA_1036]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1019_eq, calc11_set_1021_eq, calc11_set_1023_eq, calc11_set_1025_eq, calc11_set_1027_eq, calc11_set_1029_eq, calc11_finishT_1036]
  · decide +kernel

theorem valid_inline_841 : Valid inline_841 := by
  rw [eq_inline_841]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_297
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 7 (10, 8) valid_649
  subst c
  exact valid_inline_840

theorem calc11_card_1037_eq : placed 2 (2, 9) card_174 = calc11_card_1037 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1038_eq : placed 1 (2, 3) card_508 = calc11_card_1038 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1039_eq : placed 3 (8, 3) card_508 = calc11_card_1039 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1040_eq : placed 2 (2, 9) card_566 = calc11_card_1040 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1041_eq : placed 1 (2, 3) card_605 = calc11_card_1041 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1042_eq : placed 3 (8, 3) card_605 = calc11_card_1042 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1043_eq : placed 2 (1, 10) card_647 = calc11_card_1043 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1044_eq : placed 1 (0, 2) card_650 = calc11_card_1044 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1045_eq : placed 3 (10, 2) card_650 = calc11_card_1045 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1046_eq : placed 4 (9, 1) card_661 = calc11_card_1046 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1047_eq : placed 0 (2, 1) card_710 = calc11_card_1047 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1048_eq : placed 0 (1, 0) card_711 = calc11_card_1048 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1049_eq : calc11_card_1048.required ∪ ∅ = calc11_set_1049 := by decide +kernel

theorem calc11_set_1050_eq : calc11_card_1048.envelope ∪ ∅ = calc11_set_1050 := by decide +kernel

theorem calc11_set_1051_eq : calc11_card_1047.required ∪ calc11_set_1049 = calc11_set_1051 := by decide +kernel

theorem calc11_set_1052_eq : calc11_card_1047.envelope ∪ calc11_set_1050 = calc11_set_1052 := by decide +kernel

theorem calc11_set_1053_eq : calc11_card_1046.required ∪ calc11_set_1051 = calc11_set_1053 := by decide +kernel

theorem calc11_set_1054_eq : calc11_card_1046.envelope ∪ calc11_set_1052 = calc11_set_1054 := by decide +kernel

theorem calc11_set_1055_eq : inline_841.required ∪ calc11_set_1053 = calc11_set_1055 := by decide +kernel

theorem calc11_set_1056_eq : inline_841.envelope ∪ calc11_set_1054 = calc11_set_1056 := by decide +kernel

theorem calc11_set_1057_eq : calc11_card_1045.required ∪ calc11_set_1055 = calc11_set_1057 := by decide +kernel

theorem calc11_set_1058_eq : calc11_card_1045.envelope ∪ calc11_set_1056 = calc11_set_1058 := by decide +kernel

theorem calc11_set_1059_eq : calc11_card_1044.required ∪ calc11_set_1057 = calc11_set_1059 := by decide +kernel

theorem calc11_set_1060_eq : calc11_card_1044.envelope ∪ calc11_set_1058 = calc11_set_1060 := by decide +kernel

theorem calc11_set_1061_eq : calc11_card_1043.required ∪ calc11_set_1059 = calc11_set_1061 := by decide +kernel

theorem calc11_set_1062_eq : calc11_card_1043.envelope ∪ calc11_set_1060 = calc11_set_1062 := by decide +kernel

theorem calc11_set_1063_eq : calc11_card_1042.required ∪ calc11_set_1061 = calc11_set_1063 := by decide +kernel

theorem calc11_set_1064_eq : calc11_card_1042.envelope ∪ calc11_set_1062 = calc11_set_1064 := by decide +kernel

theorem calc11_set_1065_eq : calc11_card_1041.required ∪ calc11_set_1063 = calc11_set_1065 := by decide +kernel

theorem calc11_set_1066_eq : calc11_card_1041.envelope ∪ calc11_set_1064 = calc11_set_1066 := by decide +kernel

theorem calc11_set_1067_eq : calc11_card_1040.required ∪ calc11_set_1065 = calc11_set_1067 := by decide +kernel

theorem calc11_set_1068_eq : calc11_card_1040.envelope ∪ calc11_set_1066 = calc11_set_1068 := by decide +kernel

theorem calc11_set_1069_eq : calc11_card_1039.required ∪ calc11_set_1067 = calc11_set_1069 := by decide +kernel

theorem calc11_set_1070_eq : calc11_card_1039.envelope ∪ calc11_set_1068 = calc11_set_1070 := by decide +kernel

theorem calc11_set_1071_eq : calc11_card_1038.required ∪ calc11_set_1069 = calc11_set_1071 := by decide +kernel

theorem calc11_set_1072_eq : calc11_card_1038.envelope ∪ calc11_set_1070 = calc11_set_1072 := by decide +kernel

theorem calc11_set_1073_eq : calc11_card_1037.required ∪ calc11_set_1071 = calc11_set_1073 := by decide +kernel

theorem calc11_set_1074_eq : calc11_card_1037.envelope ∪ calc11_set_1072 = calc11_set_1074 := by decide +kernel

theorem calc11_set_1075_eq : calc11_card_1048.envelope ∩ calc11_card_1037.envelope = calc11_set_1075 := by decide +kernel

theorem calc11_set_1076_eq : calc11_card_1047.envelope ∩ calc11_set_1075 = calc11_set_1076 := by decide +kernel

theorem calc11_set_1077_eq : calc11_card_1046.envelope ∩ calc11_set_1076 = calc11_set_1077 := by decide +kernel

theorem calc11_set_1078_eq : inline_841.envelope ∩ calc11_set_1077 = calc11_set_1078 := by decide +kernel

theorem calc11_set_1079_eq : calc11_card_1045.envelope ∩ calc11_set_1078 = calc11_set_1079 := by decide +kernel

theorem calc11_set_1080_eq : calc11_card_1044.envelope ∩ calc11_set_1079 = calc11_set_1080 := by decide +kernel

theorem calc11_set_1081_eq : calc11_card_1043.envelope ∩ calc11_set_1080 = calc11_set_1081 := by decide +kernel

theorem calc11_set_1082_eq : calc11_card_1042.envelope ∩ calc11_set_1081 = calc11_set_1082 := by decide +kernel

theorem calc11_set_1083_eq : calc11_card_1041.envelope ∩ calc11_set_1082 = calc11_set_1083 := by decide +kernel

theorem calc11_set_1084_eq : calc11_card_1040.envelope ∩ calc11_set_1083 = calc11_set_1084 := by decide +kernel

theorem calc11_set_1085_eq : calc11_card_1039.envelope ∩ calc11_set_1084 = calc11_set_1085 := by decide +kernel

theorem calc11_set_1086_eq : calc11_card_1038.envelope ∩ calc11_set_1085 = calc11_set_1086 := by decide +kernel

theorem calc11_set_1087_eq : calc11_set_1073 ∪ calc11_set_1086 = calc11_set_1087 := by decide +kernel

theorem calc11_finishA_1088 : calc11_set_1087.erase (5, 6) = card_712.required := by decide +kernel

theorem calc11_finishT_1088 : insert (5, 6) calc11_set_1074 = card_712.envelope := by decide +kernel

theorem eq_card_712 : card_712 = combine (5, 6) [placed 2 (2, 9) card_174, placed 1 (2, 3) card_508, placed 3 (8, 3) card_508, placed 2 (2, 9) card_566, placed 1 (2, 3) card_605, placed 3 (8, 3) card_605, placed 2 (1, 10) card_647, placed 1 (0, 2) card_650, placed 3 (10, 2) card_650, inline_841, placed 4 (9, 1) card_661, placed 0 (2, 1) card_710, placed 0 (1, 0) card_711] := by
  rw [calc11_card_1037_eq, calc11_card_1038_eq, calc11_card_1039_eq, calc11_card_1040_eq, calc11_card_1041_eq, calc11_card_1042_eq, calc11_card_1043_eq, calc11_card_1044_eq, calc11_card_1045_eq, calc11_card_1046_eq, calc11_card_1047_eq, calc11_card_1048_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1049_eq, calc11_set_1051_eq, calc11_set_1053_eq, calc11_set_1055_eq, calc11_set_1057_eq, calc11_set_1059_eq, calc11_set_1061_eq, calc11_set_1063_eq, calc11_set_1065_eq, calc11_set_1067_eq, calc11_set_1069_eq, calc11_set_1071_eq, calc11_set_1073_eq, calc11_set_1075_eq, calc11_set_1076_eq, calc11_set_1077_eq, calc11_set_1078_eq, calc11_set_1079_eq, calc11_set_1080_eq, calc11_set_1081_eq, calc11_set_1082_eq, calc11_set_1083_eq, calc11_set_1084_eq, calc11_set_1085_eq, calc11_set_1086_eq, calc11_set_1087_eq, calc11_finishA_1088]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1050_eq, calc11_set_1052_eq, calc11_set_1054_eq, calc11_set_1056_eq, calc11_set_1058_eq, calc11_set_1060_eq, calc11_set_1062_eq, calc11_set_1064_eq, calc11_set_1066_eq, calc11_set_1068_eq, calc11_set_1070_eq, calc11_set_1072_eq, calc11_set_1074_eq, calc11_finishT_1088]
  · decide +kernel

theorem valid_712 : Valid card_712 := by
  rw [eq_card_712]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_174
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_566
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_647
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_650
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 2) valid_650
  rcases hc with rfl | hc
  · exact valid_inline_841
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 1) valid_661
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_710
  subst c
  exact placed_valid 0 (1, 0) valid_711

theorem calc11_card_1089_eq : placed 1 (2, 3) card_508 = calc11_card_1089 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1090_eq : placed 3 (8, 3) card_508 = calc11_card_1090 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1091_eq : placed 1 (2, 3) card_605 = calc11_card_1091 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1092_eq : placed 3 (8, 3) card_605 = calc11_card_1092 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1093_eq : placed 2 (1, 10) card_645 = calc11_card_1093 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1094_eq : placed 2 (1, 10) card_647 = calc11_card_1094 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1095_eq : placed 1 (0, 2) card_650 = calc11_card_1095 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1096_eq : placed 3 (10, 2) card_650 = calc11_card_1096 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1097_eq : placed 2 (2, 9) card_654 = calc11_card_1097 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1098_eq : placed 6 (8, 9) card_654 = calc11_card_1098 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1099_eq : placed 0 (1, 0) card_711 = calc11_card_1099 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1100_eq : calc11_card_1099.required ∪ ∅ = calc11_set_1100 := by decide +kernel

theorem calc11_set_1101_eq : calc11_card_1099.envelope ∪ ∅ = calc11_set_1101 := by decide +kernel

theorem calc11_set_1102_eq : calc11_card_1098.required ∪ calc11_set_1100 = calc11_set_1102 := by decide +kernel

theorem calc11_set_1103_eq : calc11_card_1098.envelope ∪ calc11_set_1101 = calc11_set_1103 := by decide +kernel

theorem calc11_set_1104_eq : calc11_card_1097.required ∪ calc11_set_1102 = calc11_set_1104 := by decide +kernel

theorem calc11_set_1105_eq : calc11_card_1097.envelope ∪ calc11_set_1103 = calc11_set_1105 := by decide +kernel

theorem calc11_set_1106_eq : calc11_card_1096.required ∪ calc11_set_1104 = calc11_set_1106 := by decide +kernel

theorem calc11_set_1107_eq : calc11_card_1096.envelope ∪ calc11_set_1105 = calc11_set_1107 := by decide +kernel

theorem calc11_set_1108_eq : calc11_card_1095.required ∪ calc11_set_1106 = calc11_set_1108 := by decide +kernel

theorem calc11_set_1109_eq : calc11_card_1095.envelope ∪ calc11_set_1107 = calc11_set_1109 := by decide +kernel

theorem calc11_set_1110_eq : calc11_card_1094.required ∪ calc11_set_1108 = calc11_set_1110 := by decide +kernel

theorem calc11_set_1111_eq : calc11_card_1094.envelope ∪ calc11_set_1109 = calc11_set_1111 := by decide +kernel

theorem calc11_set_1112_eq : calc11_card_1093.required ∪ calc11_set_1110 = calc11_set_1112 := by decide +kernel

theorem calc11_set_1113_eq : calc11_card_1093.envelope ∪ calc11_set_1111 = calc11_set_1113 := by decide +kernel

theorem calc11_set_1114_eq : calc11_card_1092.required ∪ calc11_set_1112 = calc11_set_1114 := by decide +kernel

theorem calc11_set_1115_eq : calc11_card_1092.envelope ∪ calc11_set_1113 = calc11_set_1115 := by decide +kernel

theorem calc11_set_1116_eq : calc11_card_1091.required ∪ calc11_set_1114 = calc11_set_1116 := by decide +kernel

theorem calc11_set_1117_eq : calc11_card_1091.envelope ∪ calc11_set_1115 = calc11_set_1117 := by decide +kernel

theorem calc11_set_1118_eq : calc11_card_1090.required ∪ calc11_set_1116 = calc11_set_1118 := by decide +kernel

theorem calc11_set_1119_eq : calc11_card_1090.envelope ∪ calc11_set_1117 = calc11_set_1119 := by decide +kernel

theorem calc11_set_1120_eq : calc11_card_1089.required ∪ calc11_set_1118 = calc11_set_1120 := by decide +kernel

theorem calc11_set_1121_eq : calc11_card_1089.envelope ∪ calc11_set_1119 = calc11_set_1121 := by decide +kernel

theorem calc11_set_1122_eq : calc11_card_1099.envelope ∩ calc11_card_1089.envelope = calc11_set_1122 := by decide +kernel

theorem calc11_set_1123_eq : calc11_card_1098.envelope ∩ calc11_set_1122 = calc11_set_1123 := by decide +kernel

theorem calc11_set_1124_eq : calc11_card_1097.envelope ∩ calc11_set_1123 = calc11_set_1124 := by decide +kernel

theorem calc11_set_1125_eq : calc11_card_1096.envelope ∩ calc11_set_1124 = calc11_set_1125 := by decide +kernel

theorem calc11_set_1126_eq : calc11_card_1095.envelope ∩ calc11_set_1125 = calc11_set_1126 := by decide +kernel

theorem calc11_set_1127_eq : calc11_card_1094.envelope ∩ calc11_set_1126 = calc11_set_1127 := by decide +kernel

theorem calc11_set_1128_eq : calc11_card_1093.envelope ∩ calc11_set_1127 = calc11_set_1128 := by decide +kernel

theorem calc11_set_1129_eq : calc11_card_1092.envelope ∩ calc11_set_1128 = calc11_set_1129 := by decide +kernel

theorem calc11_set_1130_eq : calc11_card_1091.envelope ∩ calc11_set_1129 = calc11_set_1130 := by decide +kernel

theorem calc11_set_1131_eq : calc11_card_1090.envelope ∩ calc11_set_1130 = calc11_set_1131 := by decide +kernel

theorem calc11_set_1132_eq : calc11_set_1120 ∪ calc11_set_1131 = calc11_set_1132 := by decide +kernel

theorem calc11_finishA_1133 : calc11_set_1132.erase (5, 6) = card_713.required := by decide +kernel

theorem calc11_finishT_1133 : insert (5, 6) calc11_set_1121 = card_713.envelope := by decide +kernel

theorem eq_card_713 : card_713 = combine (5, 6) [placed 1 (2, 3) card_508, placed 3 (8, 3) card_508, placed 1 (2, 3) card_605, placed 3 (8, 3) card_605, placed 2 (1, 10) card_645, placed 2 (1, 10) card_647, placed 1 (0, 2) card_650, placed 3 (10, 2) card_650, placed 2 (2, 9) card_654, placed 6 (8, 9) card_654, placed 0 (1, 0) card_711] := by
  rw [calc11_card_1089_eq, calc11_card_1090_eq, calc11_card_1091_eq, calc11_card_1092_eq, calc11_card_1093_eq, calc11_card_1094_eq, calc11_card_1095_eq, calc11_card_1096_eq, calc11_card_1097_eq, calc11_card_1098_eq, calc11_card_1099_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1100_eq, calc11_set_1102_eq, calc11_set_1104_eq, calc11_set_1106_eq, calc11_set_1108_eq, calc11_set_1110_eq, calc11_set_1112_eq, calc11_set_1114_eq, calc11_set_1116_eq, calc11_set_1118_eq, calc11_set_1120_eq, calc11_set_1122_eq, calc11_set_1123_eq, calc11_set_1124_eq, calc11_set_1125_eq, calc11_set_1126_eq, calc11_set_1127_eq, calc11_set_1128_eq, calc11_set_1129_eq, calc11_set_1130_eq, calc11_set_1131_eq, calc11_set_1132_eq, calc11_finishA_1133]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1101_eq, calc11_set_1103_eq, calc11_set_1105_eq, calc11_set_1107_eq, calc11_set_1109_eq, calc11_set_1111_eq, calc11_set_1113_eq, calc11_set_1115_eq, calc11_set_1117_eq, calc11_set_1119_eq, calc11_set_1121_eq, calc11_finishT_1133]
  · decide +kernel

theorem valid_713 : Valid card_713 := by
  rw [eq_card_713]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 3) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_645
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_647
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_650
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 2) valid_650
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_654
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 9) valid_654
  subst c
  exact placed_valid 0 (1, 0) valid_711

theorem calc11_card_1134_eq : placed 0 (2, 3) card_41 = calc11_card_1134 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1135_eq : placed 5 (0, 6) card_55 = calc11_card_1135 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1136_eq : calc11_card_1135.required ∪ ∅ = calc11_set_1136 := by decide +kernel

theorem calc11_set_1137_eq : calc11_card_1135.envelope ∪ ∅ = calc11_set_1137 := by decide +kernel

theorem calc11_set_1138_eq : calc11_card_1134.required ∪ calc11_set_1136 = calc11_set_1138 := by decide +kernel

theorem calc11_set_1139_eq : calc11_card_1134.envelope ∪ calc11_set_1137 = calc11_set_1139 := by decide +kernel

theorem calc11_set_1140_eq : calc11_card_1135.envelope ∩ calc11_card_1134.envelope = calc11_set_1140 := by decide +kernel

theorem calc11_set_1141_eq : calc11_set_1138 ∪ calc11_set_1140 = calc11_set_1141 := by decide +kernel

theorem calc11_finishA_1142 : calc11_set_1141.erase (3, 6) = inline_842.required := by decide +kernel

theorem calc11_finishT_1142 : insert (3, 6) calc11_set_1139 = inline_842.envelope := by decide +kernel

theorem eq_inline_842 : inline_842 = combine (3, 6) [placed 0 (2, 3) card_41, placed 5 (0, 6) card_55] := by
  rw [calc11_card_1134_eq, calc11_card_1135_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1136_eq, calc11_set_1138_eq, calc11_set_1140_eq, calc11_set_1141_eq, calc11_finishA_1142]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1137_eq, calc11_set_1139_eq, calc11_finishT_1142]
  · decide +kernel

theorem valid_inline_842 : Valid inline_842 := by
  rw [eq_inline_842]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_41
  subst c
  exact placed_valid 5 (0, 6) valid_55

theorem calc11_card_1143_eq : placed 4 (3, 2) card_15 = calc11_card_1143 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1144_eq : placed 5 (0, 6) card_88 = calc11_card_1144 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1145_eq : inline_842.required ∪ ∅ = calc11_set_1145 := by decide +kernel

theorem calc11_set_1146_eq : inline_842.envelope ∪ ∅ = calc11_set_1146 := by decide +kernel

theorem calc11_set_1147_eq : calc11_card_1144.required ∪ calc11_set_1145 = calc11_set_1147 := by decide +kernel

theorem calc11_set_1148_eq : calc11_card_1144.envelope ∪ calc11_set_1146 = calc11_set_1148 := by decide +kernel

theorem calc11_set_1149_eq : calc11_card_1143.required ∪ calc11_set_1147 = calc11_set_1149 := by decide +kernel

theorem calc11_set_1150_eq : calc11_card_1143.envelope ∪ calc11_set_1148 = calc11_set_1150 := by decide +kernel

theorem calc11_set_1151_eq : inline_842.envelope ∩ calc11_card_1143.envelope = calc11_set_1151 := by decide +kernel

theorem calc11_set_1152_eq : calc11_card_1144.envelope ∩ calc11_set_1151 = calc11_set_1152 := by decide +kernel

theorem calc11_set_1153_eq : calc11_set_1149 ∪ calc11_set_1152 = calc11_set_1153 := by decide +kernel

theorem calc11_finishA_1154 : calc11_set_1153.erase (3, 3) = card_714.required := by decide +kernel

theorem calc11_finishT_1154 : insert (3, 3) calc11_set_1150 = card_714.envelope := by decide +kernel

theorem eq_card_714 : card_714 = combine (3, 3) [placed 4 (3, 2) card_15, placed 5 (0, 6) card_88, inline_842] := by
  rw [calc11_card_1143_eq, calc11_card_1144_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1145_eq, calc11_set_1147_eq, calc11_set_1149_eq, calc11_set_1151_eq, calc11_set_1152_eq, calc11_set_1153_eq, calc11_finishA_1154]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1146_eq, calc11_set_1148_eq, calc11_set_1150_eq, calc11_finishT_1154]
  · decide +kernel

theorem valid_714 : Valid card_714 := by
  rw [eq_card_714]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_88
  subst c
  exact valid_inline_842

theorem calc11_card_1155_eq : placed 6 (5, 8) card_53 = calc11_card_1155 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1156_eq : placed 0 (4, 2) card_53 = calc11_card_1156 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1157_eq : placed 0 (2, 2) card_111 = calc11_card_1157 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1158_eq : placed 1 (2, 4) card_394 = calc11_card_1158 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1159_eq : calc11_card_1158.required ∪ ∅ = calc11_set_1159 := by decide +kernel

theorem calc11_set_1160_eq : calc11_card_1158.envelope ∪ ∅ = calc11_set_1160 := by decide +kernel

theorem calc11_set_1161_eq : calc11_card_1157.required ∪ calc11_set_1159 = calc11_set_1161 := by decide +kernel

theorem calc11_set_1162_eq : calc11_card_1157.envelope ∪ calc11_set_1160 = calc11_set_1162 := by decide +kernel

theorem calc11_set_1163_eq : calc11_card_1156.required ∪ calc11_set_1161 = calc11_set_1163 := by decide +kernel

theorem calc11_set_1164_eq : calc11_card_1156.envelope ∪ calc11_set_1162 = calc11_set_1164 := by decide +kernel

theorem calc11_set_1165_eq : calc11_card_1155.required ∪ calc11_set_1163 = calc11_set_1165 := by decide +kernel

theorem calc11_set_1166_eq : calc11_card_1155.envelope ∪ calc11_set_1164 = calc11_set_1166 := by decide +kernel

theorem calc11_set_1167_eq : calc11_card_1158.envelope ∩ calc11_card_1155.envelope = calc11_set_1167 := by decide +kernel

theorem calc11_set_1168_eq : calc11_card_1157.envelope ∩ calc11_set_1167 = calc11_set_1168 := by decide +kernel

theorem calc11_set_1169_eq : calc11_card_1156.envelope ∩ calc11_set_1168 = calc11_set_1169 := by decide +kernel

theorem calc11_set_1170_eq : calc11_set_1165 ∪ calc11_set_1169 = calc11_set_1170 := by decide +kernel

theorem calc11_finishA_1171 : calc11_set_1170.erase (4, 4) = inline_843.required := by decide +kernel

theorem calc11_finishT_1171 : insert (4, 4) calc11_set_1166 = inline_843.envelope := by decide +kernel

theorem eq_inline_843 : inline_843 = combine (4, 4) [placed 6 (5, 8) card_53, placed 0 (4, 2) card_53, placed 0 (2, 2) card_111, placed 1 (2, 4) card_394] := by
  rw [calc11_card_1155_eq, calc11_card_1156_eq, calc11_card_1157_eq, calc11_card_1158_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1159_eq, calc11_set_1161_eq, calc11_set_1163_eq, calc11_set_1165_eq, calc11_set_1167_eq, calc11_set_1168_eq, calc11_set_1169_eq, calc11_set_1170_eq, calc11_finishA_1171]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1160_eq, calc11_set_1162_eq, calc11_set_1164_eq, calc11_set_1166_eq, calc11_finishT_1171]
  · decide +kernel

theorem valid_inline_843 : Valid inline_843 := by
  rw [eq_inline_843]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_111
  subst c
  exact placed_valid 1 (2, 4) valid_394

theorem calc11_card_1172_eq : placed 1 (2, 5) card_44 = calc11_card_1172 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1173_eq : placed 1 (2, 5) card_52 = calc11_card_1173 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1174_eq : placed 4 (6, 3) card_134 = calc11_card_1174 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1175_eq : inline_843.required ∪ ∅ = calc11_set_1175 := by decide +kernel

theorem calc11_set_1176_eq : inline_843.envelope ∪ ∅ = calc11_set_1176 := by decide +kernel

theorem calc11_set_1177_eq : calc11_card_1174.required ∪ calc11_set_1175 = calc11_set_1177 := by decide +kernel

theorem calc11_set_1178_eq : calc11_card_1174.envelope ∪ calc11_set_1176 = calc11_set_1178 := by decide +kernel

theorem calc11_set_1179_eq : calc11_card_1173.required ∪ calc11_set_1177 = calc11_set_1179 := by decide +kernel

theorem calc11_set_1180_eq : calc11_card_1173.envelope ∪ calc11_set_1178 = calc11_set_1180 := by decide +kernel

theorem calc11_set_1181_eq : calc11_card_1172.required ∪ calc11_set_1179 = calc11_set_1181 := by decide +kernel

theorem calc11_set_1182_eq : calc11_card_1172.envelope ∪ calc11_set_1180 = calc11_set_1182 := by decide +kernel

theorem calc11_set_1183_eq : inline_843.envelope ∩ calc11_card_1172.envelope = calc11_set_1183 := by decide +kernel

theorem calc11_set_1184_eq : calc11_card_1174.envelope ∩ calc11_set_1183 = calc11_set_1184 := by decide +kernel

theorem calc11_set_1185_eq : calc11_card_1173.envelope ∩ calc11_set_1184 = calc11_set_1185 := by decide +kernel

theorem calc11_set_1186_eq : calc11_set_1181 ∪ calc11_set_1185 = calc11_set_1186 := by decide +kernel

theorem calc11_finishA_1187 : calc11_set_1186.erase (3, 5) = inline_844.required := by decide +kernel

theorem calc11_finishT_1187 : insert (3, 5) calc11_set_1182 = inline_844.envelope := by decide +kernel

theorem eq_inline_844 : inline_844 = combine (3, 5) [placed 1 (2, 5) card_44, placed 1 (2, 5) card_52, placed 4 (6, 3) card_134, inline_843] := by
  rw [calc11_card_1172_eq, calc11_card_1173_eq, calc11_card_1174_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1175_eq, calc11_set_1177_eq, calc11_set_1179_eq, calc11_set_1181_eq, calc11_set_1183_eq, calc11_set_1184_eq, calc11_set_1185_eq, calc11_set_1186_eq, calc11_finishA_1187]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1176_eq, calc11_set_1178_eq, calc11_set_1180_eq, calc11_set_1182_eq, calc11_finishT_1187]
  · decide +kernel

theorem valid_inline_844 : Valid inline_844 := by
  rw [eq_inline_844]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_134
  subst c
  exact valid_inline_843

theorem calc11_card_1188_eq : placed 5 (4, 6) card_30 = calc11_card_1188 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1189_eq : placed 0 (4, 3) card_110 = calc11_card_1189 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1190_eq : placed 1 (3, 4) card_296 = calc11_card_1190 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1191_eq : placed 0 (4, 3) card_511 = calc11_card_1191 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1192_eq : calc11_card_1191.required ∪ ∅ = calc11_set_1192 := by decide +kernel

theorem calc11_set_1193_eq : calc11_card_1191.envelope ∪ ∅ = calc11_set_1193 := by decide +kernel

theorem calc11_set_1194_eq : calc11_card_1190.required ∪ calc11_set_1192 = calc11_set_1194 := by decide +kernel

theorem calc11_set_1195_eq : calc11_card_1190.envelope ∪ calc11_set_1193 = calc11_set_1195 := by decide +kernel

theorem calc11_set_1196_eq : calc11_card_1189.required ∪ calc11_set_1194 = calc11_set_1196 := by decide +kernel

theorem calc11_set_1197_eq : calc11_card_1189.envelope ∪ calc11_set_1195 = calc11_set_1197 := by decide +kernel

theorem calc11_set_1198_eq : calc11_card_1188.required ∪ calc11_set_1196 = calc11_set_1198 := by decide +kernel

theorem calc11_set_1199_eq : calc11_card_1188.envelope ∪ calc11_set_1197 = calc11_set_1199 := by decide +kernel

theorem calc11_set_1200_eq : calc11_card_1191.envelope ∩ calc11_card_1188.envelope = calc11_set_1200 := by decide +kernel

theorem calc11_set_1201_eq : calc11_card_1190.envelope ∩ calc11_set_1200 = calc11_set_1201 := by decide +kernel

theorem calc11_set_1202_eq : calc11_card_1189.envelope ∩ calc11_set_1201 = calc11_set_1202 := by decide +kernel

theorem calc11_set_1203_eq : calc11_set_1198 ∪ calc11_set_1202 = calc11_set_1203 := by decide +kernel

theorem calc11_finishA_1204 : calc11_set_1203.erase (7, 6) = inline_845.required := by decide +kernel

theorem calc11_finishT_1204 : insert (7, 6) calc11_set_1199 = inline_845.envelope := by decide +kernel

theorem eq_inline_845 : inline_845 = combine (7, 6) [placed 5 (4, 6) card_30, placed 0 (4, 3) card_110, placed 1 (3, 4) card_296, placed 0 (4, 3) card_511] := by
  rw [calc11_card_1188_eq, calc11_card_1189_eq, calc11_card_1190_eq, calc11_card_1191_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1192_eq, calc11_set_1194_eq, calc11_set_1196_eq, calc11_set_1198_eq, calc11_set_1200_eq, calc11_set_1201_eq, calc11_set_1202_eq, calc11_set_1203_eq, calc11_finishA_1204]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1193_eq, calc11_set_1195_eq, calc11_set_1197_eq, calc11_set_1199_eq, calc11_finishT_1204]
  · decide +kernel

theorem valid_inline_845 : Valid inline_845 := by
  rw [eq_inline_845]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 6) valid_30
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_110
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_296
  subst c
  exact placed_valid 0 (4, 3) valid_511

theorem calc11_card_1205_eq : placed 1 (3, 5) card_22 = calc11_card_1205 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1206_eq : placed 1 (4, 5) card_74 = calc11_card_1206 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1207_eq : placed 0 (3, 1) card_325 = calc11_card_1207 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1208_eq : inline_845.required ∪ ∅ = calc11_set_1208 := by decide +kernel

theorem calc11_set_1209_eq : inline_845.envelope ∪ ∅ = calc11_set_1209 := by decide +kernel

theorem calc11_set_1210_eq : calc11_card_1207.required ∪ calc11_set_1208 = calc11_set_1210 := by decide +kernel

theorem calc11_set_1211_eq : calc11_card_1207.envelope ∪ calc11_set_1209 = calc11_set_1211 := by decide +kernel

theorem calc11_set_1212_eq : calc11_card_1206.required ∪ calc11_set_1210 = calc11_set_1212 := by decide +kernel

theorem calc11_set_1213_eq : calc11_card_1206.envelope ∪ calc11_set_1211 = calc11_set_1213 := by decide +kernel

theorem calc11_set_1214_eq : calc11_card_1205.required ∪ calc11_set_1212 = calc11_set_1214 := by decide +kernel

theorem calc11_set_1215_eq : calc11_card_1205.envelope ∪ calc11_set_1213 = calc11_set_1215 := by decide +kernel

theorem calc11_set_1216_eq : inline_845.envelope ∩ calc11_card_1205.envelope = calc11_set_1216 := by decide +kernel

theorem calc11_set_1217_eq : calc11_card_1207.envelope ∩ calc11_set_1216 = calc11_set_1217 := by decide +kernel

theorem calc11_set_1218_eq : calc11_card_1206.envelope ∩ calc11_set_1217 = calc11_set_1218 := by decide +kernel

theorem calc11_set_1219_eq : calc11_set_1214 ∪ calc11_set_1218 = calc11_set_1219 := by decide +kernel

theorem calc11_finishA_1220 : calc11_set_1219.erase (7, 5) = inline_846.required := by decide +kernel

theorem calc11_finishT_1220 : insert (7, 5) calc11_set_1215 = inline_846.envelope := by decide +kernel

theorem eq_inline_846 : inline_846 = combine (7, 5) [placed 1 (3, 5) card_22, placed 1 (4, 5) card_74, placed 0 (3, 1) card_325, inline_845] := by
  rw [calc11_card_1205_eq, calc11_card_1206_eq, calc11_card_1207_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1208_eq, calc11_set_1210_eq, calc11_set_1212_eq, calc11_set_1214_eq, calc11_set_1216_eq, calc11_set_1217_eq, calc11_set_1218_eq, calc11_set_1219_eq, calc11_finishA_1220]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1209_eq, calc11_set_1211_eq, calc11_set_1213_eq, calc11_set_1215_eq, calc11_finishT_1220]
  · decide +kernel

theorem valid_inline_846 : Valid inline_846 := by
  rw [eq_inline_846]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 5) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 5) valid_74
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_325
  subst c
  exact valid_inline_845

theorem calc11_card_1221_eq : placed 4 (7, 3) card_361 = calc11_card_1221 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1222_eq : placed 3 (8, 5) card_408 = calc11_card_1222 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1223_eq : placed 7 (8, 9) card_621 = calc11_card_1223 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1224_eq : placed 1 (0, 3) card_714 = calc11_card_1224 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1225_eq : inline_846.required ∪ ∅ = calc11_set_1225 := by decide +kernel

theorem calc11_set_1226_eq : inline_846.envelope ∪ ∅ = calc11_set_1226 := by decide +kernel

theorem calc11_set_1227_eq : calc11_card_1224.required ∪ calc11_set_1225 = calc11_set_1227 := by decide +kernel

theorem calc11_set_1228_eq : calc11_card_1224.envelope ∪ calc11_set_1226 = calc11_set_1228 := by decide +kernel

theorem calc11_set_1229_eq : calc11_card_1223.required ∪ calc11_set_1227 = calc11_set_1229 := by decide +kernel

theorem calc11_set_1230_eq : calc11_card_1223.envelope ∪ calc11_set_1228 = calc11_set_1230 := by decide +kernel

theorem calc11_set_1231_eq : calc11_card_1222.required ∪ calc11_set_1229 = calc11_set_1231 := by decide +kernel

theorem calc11_set_1232_eq : calc11_card_1222.envelope ∪ calc11_set_1230 = calc11_set_1232 := by decide +kernel

theorem calc11_set_1233_eq : calc11_card_1221.required ∪ calc11_set_1231 = calc11_set_1233 := by decide +kernel

theorem calc11_set_1234_eq : calc11_card_1221.envelope ∪ calc11_set_1232 = calc11_set_1234 := by decide +kernel

theorem calc11_set_1235_eq : inline_846.envelope ∩ calc11_card_1221.envelope = calc11_set_1235 := by decide +kernel

theorem calc11_set_1236_eq : calc11_card_1224.envelope ∩ calc11_set_1235 = calc11_set_1236 := by decide +kernel

theorem calc11_set_1237_eq : calc11_card_1223.envelope ∩ calc11_set_1236 = calc11_set_1237 := by decide +kernel

theorem calc11_set_1238_eq : calc11_card_1222.envelope ∩ calc11_set_1237 = calc11_set_1238 := by decide +kernel

theorem calc11_set_1239_eq : calc11_set_1233 ∪ calc11_set_1238 = calc11_set_1239 := by decide +kernel

theorem calc11_finishA_1240 : calc11_set_1239.erase (4, 6) = inline_847.required := by decide +kernel

theorem calc11_finishT_1240 : insert (4, 6) calc11_set_1234 = inline_847.envelope := by decide +kernel

theorem eq_inline_847 : inline_847 = combine (4, 6) [placed 4 (7, 3) card_361, placed 3 (8, 5) card_408, placed 7 (8, 9) card_621, placed 1 (0, 3) card_714, inline_846] := by
  rw [calc11_card_1221_eq, calc11_card_1222_eq, calc11_card_1223_eq, calc11_card_1224_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1225_eq, calc11_set_1227_eq, calc11_set_1229_eq, calc11_set_1231_eq, calc11_set_1233_eq, calc11_set_1235_eq, calc11_set_1236_eq, calc11_set_1237_eq, calc11_set_1238_eq, calc11_set_1239_eq, calc11_finishA_1240]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1226_eq, calc11_set_1228_eq, calc11_set_1230_eq, calc11_set_1232_eq, calc11_set_1234_eq, calc11_finishT_1240]
  · decide +kernel

theorem valid_inline_847 : Valid inline_847 := by
  rw [eq_inline_847]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_361
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_408
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 9) valid_621
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_714
  subst c
  exact valid_inline_846

theorem calc11_card_1241_eq : placed 2 (2, 9) card_523 = calc11_card_1241 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1242_eq : placed 1 (0, 3) card_532 = calc11_card_1242 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1243_eq : placed 6 (8, 9) card_536 = calc11_card_1243 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1244_eq : placed 6 (6, 10) card_545 = calc11_card_1244 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1245_eq : placed 2 (2, 10) card_655 = calc11_card_1245 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1246_eq : placed 1 (0, 1) card_664 = calc11_card_1246 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1247_eq : inline_847.required ∪ ∅ = calc11_set_1247 := by decide +kernel

theorem calc11_set_1248_eq : inline_847.envelope ∪ ∅ = calc11_set_1248 := by decide +kernel

theorem calc11_set_1249_eq : inline_844.required ∪ calc11_set_1247 = calc11_set_1249 := by decide +kernel

theorem calc11_set_1250_eq : inline_844.envelope ∪ calc11_set_1248 = calc11_set_1250 := by decide +kernel

theorem calc11_set_1251_eq : calc11_card_1246.required ∪ calc11_set_1249 = calc11_set_1251 := by decide +kernel

theorem calc11_set_1252_eq : calc11_card_1246.envelope ∪ calc11_set_1250 = calc11_set_1252 := by decide +kernel

theorem calc11_set_1253_eq : calc11_card_1245.required ∪ calc11_set_1251 = calc11_set_1253 := by decide +kernel

theorem calc11_set_1254_eq : calc11_card_1245.envelope ∪ calc11_set_1252 = calc11_set_1254 := by decide +kernel

theorem calc11_set_1255_eq : calc11_card_1244.required ∪ calc11_set_1253 = calc11_set_1255 := by decide +kernel

theorem calc11_set_1256_eq : calc11_card_1244.envelope ∪ calc11_set_1254 = calc11_set_1256 := by decide +kernel

theorem calc11_set_1257_eq : calc11_card_1243.required ∪ calc11_set_1255 = calc11_set_1257 := by decide +kernel

theorem calc11_set_1258_eq : calc11_card_1243.envelope ∪ calc11_set_1256 = calc11_set_1258 := by decide +kernel

theorem calc11_set_1259_eq : calc11_card_1242.required ∪ calc11_set_1257 = calc11_set_1259 := by decide +kernel

theorem calc11_set_1260_eq : calc11_card_1242.envelope ∪ calc11_set_1258 = calc11_set_1260 := by decide +kernel

theorem calc11_set_1261_eq : calc11_card_1241.required ∪ calc11_set_1259 = calc11_set_1261 := by decide +kernel

theorem calc11_set_1262_eq : calc11_card_1241.envelope ∪ calc11_set_1260 = calc11_set_1262 := by decide +kernel

theorem calc11_set_1263_eq : inline_847.envelope ∩ calc11_card_1241.envelope = calc11_set_1263 := by decide +kernel

theorem calc11_set_1264_eq : inline_844.envelope ∩ calc11_set_1263 = calc11_set_1264 := by decide +kernel

theorem calc11_set_1265_eq : calc11_card_1246.envelope ∩ calc11_set_1264 = calc11_set_1265 := by decide +kernel

theorem calc11_set_1266_eq : calc11_card_1245.envelope ∩ calc11_set_1265 = calc11_set_1266 := by decide +kernel

theorem calc11_set_1267_eq : calc11_card_1244.envelope ∩ calc11_set_1266 = calc11_set_1267 := by decide +kernel

theorem calc11_set_1268_eq : calc11_card_1243.envelope ∩ calc11_set_1267 = calc11_set_1268 := by decide +kernel

theorem calc11_set_1269_eq : calc11_card_1242.envelope ∩ calc11_set_1268 = calc11_set_1269 := by decide +kernel

theorem calc11_set_1270_eq : calc11_set_1261 ∪ calc11_set_1269 = calc11_set_1270 := by decide +kernel

theorem calc11_finishA_1271 : calc11_set_1270.erase (5, 6) = card_715.required := by decide +kernel

theorem calc11_finishT_1271 : insert (5, 6) calc11_set_1262 = card_715.envelope := by decide +kernel

theorem eq_card_715 : card_715 = combine (5, 6) [placed 2 (2, 9) card_523, placed 1 (0, 3) card_532, placed 6 (8, 9) card_536, placed 6 (6, 10) card_545, placed 2 (2, 10) card_655, placed 1 (0, 1) card_664, inline_844, inline_847] := by
  rw [calc11_card_1241_eq, calc11_card_1242_eq, calc11_card_1243_eq, calc11_card_1244_eq, calc11_card_1245_eq, calc11_card_1246_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1247_eq, calc11_set_1249_eq, calc11_set_1251_eq, calc11_set_1253_eq, calc11_set_1255_eq, calc11_set_1257_eq, calc11_set_1259_eq, calc11_set_1261_eq, calc11_set_1263_eq, calc11_set_1264_eq, calc11_set_1265_eq, calc11_set_1266_eq, calc11_set_1267_eq, calc11_set_1268_eq, calc11_set_1269_eq, calc11_set_1270_eq, calc11_finishA_1271]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1248_eq, calc11_set_1250_eq, calc11_set_1252_eq, calc11_set_1254_eq, calc11_set_1256_eq, calc11_set_1258_eq, calc11_set_1260_eq, calc11_set_1262_eq, calc11_finishT_1271]
  · decide +kernel

theorem valid_715 : Valid card_715 := by
  rw [eq_card_715]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 9) valid_523
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_532
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 9) valid_536
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 10) valid_545
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 10) valid_655
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_664
  rcases hc with rfl | hc
  · exact valid_inline_844
  subst c
  exact valid_inline_847

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

theorem calc11_card_1297_eq : placed 1 (2, 5) card_192 = calc11_card_1297 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1298_eq : placed 7 (8, 7) card_192 = calc11_card_1298 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1299_eq : placed 4 (10, 1) card_550 = calc11_card_1299 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1300_eq : placed 2 (0, 11) card_550 = calc11_card_1300 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1301_eq : placed 0 (3, 3) card_578 = calc11_card_1301 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1302_eq : placed 6 (7, 9) card_578 = calc11_card_1302 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1303_eq : placed 1 (1, 3) card_622 = calc11_card_1303 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1304_eq : placed 7 (9, 9) card_622 = calc11_card_1304 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1305_eq : placed 0 (0, 1) card_716 = calc11_card_1305 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1306_eq : placed 6 (10, 11) card_716 = calc11_card_1306 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1307_eq : calc11_card_1306.required ∪ ∅ = calc11_set_1307 := by decide +kernel

theorem calc11_set_1308_eq : calc11_card_1306.envelope ∪ ∅ = calc11_set_1308 := by decide +kernel

theorem calc11_set_1309_eq : calc11_card_1305.required ∪ calc11_set_1307 = calc11_set_1309 := by decide +kernel

theorem calc11_set_1310_eq : calc11_card_1305.envelope ∪ calc11_set_1308 = calc11_set_1310 := by decide +kernel

theorem calc11_set_1311_eq : calc11_card_1304.required ∪ calc11_set_1309 = calc11_set_1311 := by decide +kernel

theorem calc11_set_1312_eq : calc11_card_1304.envelope ∪ calc11_set_1310 = calc11_set_1312 := by decide +kernel

theorem calc11_set_1313_eq : calc11_card_1303.required ∪ calc11_set_1311 = calc11_set_1313 := by decide +kernel

theorem calc11_set_1314_eq : calc11_card_1303.envelope ∪ calc11_set_1312 = calc11_set_1314 := by decide +kernel

theorem calc11_set_1315_eq : calc11_card_1302.required ∪ calc11_set_1313 = calc11_set_1315 := by decide +kernel

theorem calc11_set_1316_eq : calc11_card_1302.envelope ∪ calc11_set_1314 = calc11_set_1316 := by decide +kernel

theorem calc11_set_1317_eq : calc11_card_1301.required ∪ calc11_set_1315 = calc11_set_1317 := by decide +kernel

theorem calc11_set_1318_eq : calc11_card_1301.envelope ∪ calc11_set_1316 = calc11_set_1318 := by decide +kernel

theorem calc11_set_1319_eq : calc11_card_1300.required ∪ calc11_set_1317 = calc11_set_1319 := by decide +kernel

theorem calc11_set_1320_eq : calc11_card_1300.envelope ∪ calc11_set_1318 = calc11_set_1320 := by decide +kernel

theorem calc11_set_1321_eq : calc11_card_1299.required ∪ calc11_set_1319 = calc11_set_1321 := by decide +kernel

theorem calc11_set_1322_eq : calc11_card_1299.envelope ∪ calc11_set_1320 = calc11_set_1322 := by decide +kernel

theorem calc11_set_1323_eq : calc11_card_1298.required ∪ calc11_set_1321 = calc11_set_1323 := by decide +kernel

theorem calc11_set_1324_eq : calc11_card_1298.envelope ∪ calc11_set_1322 = calc11_set_1324 := by decide +kernel

theorem calc11_set_1325_eq : calc11_card_1297.required ∪ calc11_set_1323 = calc11_set_1325 := by decide +kernel

theorem calc11_set_1326_eq : calc11_card_1297.envelope ∪ calc11_set_1324 = calc11_set_1326 := by decide +kernel

theorem calc11_set_1327_eq : calc11_card_1306.envelope ∩ calc11_card_1297.envelope = calc11_set_1327 := by decide +kernel

theorem calc11_set_1328_eq : calc11_card_1305.envelope ∩ calc11_set_1327 = calc11_set_1328 := by decide +kernel

theorem calc11_set_1329_eq : calc11_card_1304.envelope ∩ calc11_set_1328 = calc11_set_1329 := by decide +kernel

theorem calc11_set_1330_eq : calc11_card_1303.envelope ∩ calc11_set_1329 = calc11_set_1330 := by decide +kernel

theorem calc11_set_1331_eq : calc11_card_1302.envelope ∩ calc11_set_1330 = calc11_set_1331 := by decide +kernel

theorem calc11_set_1332_eq : calc11_card_1301.envelope ∩ calc11_set_1331 = calc11_set_1332 := by decide +kernel

theorem calc11_set_1333_eq : calc11_card_1300.envelope ∩ calc11_set_1332 = calc11_set_1333 := by decide +kernel

theorem calc11_set_1334_eq : calc11_card_1299.envelope ∩ calc11_set_1333 = calc11_set_1334 := by decide +kernel

theorem calc11_set_1335_eq : calc11_card_1298.envelope ∩ calc11_set_1334 = calc11_set_1335 := by decide +kernel

theorem calc11_set_1336_eq : calc11_set_1325 ∪ calc11_set_1335 = calc11_set_1336 := by decide +kernel

theorem calc11_finishA_1337 : calc11_set_1336.erase (6, 6) = card_717.required := by decide +kernel

theorem calc11_finishT_1337 : insert (6, 6) calc11_set_1326 = card_717.envelope := by decide +kernel

theorem eq_card_717 : card_717 = combine (6, 6) [placed 1 (2, 5) card_192, placed 7 (8, 7) card_192, placed 4 (10, 1) card_550, placed 2 (0, 11) card_550, placed 0 (3, 3) card_578, placed 6 (7, 9) card_578, placed 1 (1, 3) card_622, placed 7 (9, 9) card_622, placed 0 (0, 1) card_716, placed 6 (10, 11) card_716] := by
  rw [calc11_card_1297_eq, calc11_card_1298_eq, calc11_card_1299_eq, calc11_card_1300_eq, calc11_card_1301_eq, calc11_card_1302_eq, calc11_card_1303_eq, calc11_card_1304_eq, calc11_card_1305_eq, calc11_card_1306_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1307_eq, calc11_set_1309_eq, calc11_set_1311_eq, calc11_set_1313_eq, calc11_set_1315_eq, calc11_set_1317_eq, calc11_set_1319_eq, calc11_set_1321_eq, calc11_set_1323_eq, calc11_set_1325_eq, calc11_set_1327_eq, calc11_set_1328_eq, calc11_set_1329_eq, calc11_set_1330_eq, calc11_set_1331_eq, calc11_set_1332_eq, calc11_set_1333_eq, calc11_set_1334_eq, calc11_set_1335_eq, calc11_set_1336_eq, calc11_finishA_1337]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1308_eq, calc11_set_1310_eq, calc11_set_1312_eq, calc11_set_1314_eq, calc11_set_1316_eq, calc11_set_1318_eq, calc11_set_1320_eq, calc11_set_1322_eq, calc11_set_1324_eq, calc11_set_1326_eq, calc11_finishT_1337]
  · decide +kernel

theorem valid_717 : Valid card_717 := by
  rw [eq_card_717]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 7) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 4 (10, 1) valid_550
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 11) valid_550
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_578
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 9) valid_578
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_622
  rcases hc with rfl | hc
  · exact placed_valid 7 (9, 9) valid_622
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_716
  subst c
  exact placed_valid 6 (10, 11) valid_716

theorem calc11_card_1338_eq : placed 3 (8, 5) card_44 = calc11_card_1338 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1339_eq : placed 3 (8, 5) card_52 = calc11_card_1339 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1340_eq : placed 6 (8, 7) card_155 = calc11_card_1340 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1341_eq : placed 5 (2, 8) card_341 = calc11_card_1341 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1342_eq : calc11_card_1341.required ∪ ∅ = calc11_set_1342 := by decide +kernel

theorem calc11_set_1343_eq : calc11_card_1341.envelope ∪ ∅ = calc11_set_1343 := by decide +kernel

theorem calc11_set_1344_eq : calc11_card_1340.required ∪ calc11_set_1342 = calc11_set_1344 := by decide +kernel

theorem calc11_set_1345_eq : calc11_card_1340.envelope ∪ calc11_set_1343 = calc11_set_1345 := by decide +kernel

theorem calc11_set_1346_eq : calc11_card_1339.required ∪ calc11_set_1344 = calc11_set_1346 := by decide +kernel

theorem calc11_set_1347_eq : calc11_card_1339.envelope ∪ calc11_set_1345 = calc11_set_1347 := by decide +kernel

theorem calc11_set_1348_eq : calc11_card_1338.required ∪ calc11_set_1346 = calc11_set_1348 := by decide +kernel

theorem calc11_set_1349_eq : calc11_card_1338.envelope ∪ calc11_set_1347 = calc11_set_1349 := by decide +kernel

theorem calc11_set_1350_eq : calc11_card_1341.envelope ∩ calc11_card_1338.envelope = calc11_set_1350 := by decide +kernel

theorem calc11_set_1351_eq : calc11_card_1340.envelope ∩ calc11_set_1350 = calc11_set_1351 := by decide +kernel

theorem calc11_set_1352_eq : calc11_card_1339.envelope ∩ calc11_set_1351 = calc11_set_1352 := by decide +kernel

theorem calc11_set_1353_eq : calc11_set_1348 ∪ calc11_set_1352 = calc11_set_1353 := by decide +kernel

theorem calc11_finishA_1354 : calc11_set_1353.erase (6, 5) = inline_849.required := by decide +kernel

theorem calc11_finishT_1354 : insert (6, 5) calc11_set_1349 = inline_849.envelope := by decide +kernel

theorem eq_inline_849 : inline_849 = combine (6, 5) [placed 3 (8, 5) card_44, placed 3 (8, 5) card_52, placed 6 (8, 7) card_155, placed 5 (2, 8) card_341] := by
  rw [calc11_card_1338_eq, calc11_card_1339_eq, calc11_card_1340_eq, calc11_card_1341_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1342_eq, calc11_set_1344_eq, calc11_set_1346_eq, calc11_set_1348_eq, calc11_set_1350_eq, calc11_set_1351_eq, calc11_set_1352_eq, calc11_set_1353_eq, calc11_finishA_1354]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1343_eq, calc11_set_1345_eq, calc11_set_1347_eq, calc11_set_1349_eq, calc11_finishT_1354]
  · decide +kernel

theorem valid_inline_849 : Valid inline_849 := by
  rw [eq_inline_849]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 7) valid_155
  subst c
  exact placed_valid 5 (2, 8) valid_341

theorem calc11_card_1355_eq : placed 0 (2, 2) card_452 = calc11_card_1355 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1356_eq : placed 4 (10, 0) card_520 = calc11_card_1356 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1357_eq : placed 2 (5, 9) card_587 = calc11_card_1357 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1358_eq : placed 7 (8, 6) card_612 = calc11_card_1358 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1359_eq : placed 0 (2, 1) card_633 = calc11_card_1359 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1360_eq : calc11_card_1359.required ∪ ∅ = calc11_set_1360 := by decide +kernel

theorem calc11_set_1361_eq : calc11_card_1359.envelope ∪ ∅ = calc11_set_1361 := by decide +kernel

theorem calc11_set_1362_eq : calc11_card_1358.required ∪ calc11_set_1360 = calc11_set_1362 := by decide +kernel

theorem calc11_set_1363_eq : calc11_card_1358.envelope ∪ calc11_set_1361 = calc11_set_1363 := by decide +kernel

theorem calc11_set_1364_eq : calc11_card_1357.required ∪ calc11_set_1362 = calc11_set_1364 := by decide +kernel

theorem calc11_set_1365_eq : calc11_card_1357.envelope ∪ calc11_set_1363 = calc11_set_1365 := by decide +kernel

theorem calc11_set_1366_eq : calc11_card_1356.required ∪ calc11_set_1364 = calc11_set_1366 := by decide +kernel

theorem calc11_set_1367_eq : calc11_card_1356.envelope ∪ calc11_set_1365 = calc11_set_1367 := by decide +kernel

theorem calc11_set_1368_eq : calc11_card_1355.required ∪ calc11_set_1366 = calc11_set_1368 := by decide +kernel

theorem calc11_set_1369_eq : calc11_card_1355.envelope ∪ calc11_set_1367 = calc11_set_1369 := by decide +kernel

theorem calc11_set_1370_eq : calc11_card_1359.envelope ∩ calc11_card_1355.envelope = calc11_set_1370 := by decide +kernel

theorem calc11_set_1371_eq : calc11_card_1358.envelope ∩ calc11_set_1370 = calc11_set_1371 := by decide +kernel

theorem calc11_set_1372_eq : calc11_card_1357.envelope ∩ calc11_set_1371 = calc11_set_1372 := by decide +kernel

theorem calc11_set_1373_eq : calc11_card_1356.envelope ∩ calc11_set_1372 = calc11_set_1373 := by decide +kernel

theorem calc11_set_1374_eq : calc11_set_1368 ∪ calc11_set_1373 = calc11_set_1374 := by decide +kernel

theorem calc11_finishA_1375 : calc11_set_1374.erase (7, 6) = inline_850.required := by decide +kernel

theorem calc11_finishT_1375 : insert (7, 6) calc11_set_1369 = inline_850.envelope := by decide +kernel

theorem eq_inline_850 : inline_850 = combine (7, 6) [placed 0 (2, 2) card_452, placed 4 (10, 0) card_520, placed 2 (5, 9) card_587, placed 7 (8, 6) card_612, placed 0 (2, 1) card_633] := by
  rw [calc11_card_1355_eq, calc11_card_1356_eq, calc11_card_1357_eq, calc11_card_1358_eq, calc11_card_1359_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1360_eq, calc11_set_1362_eq, calc11_set_1364_eq, calc11_set_1366_eq, calc11_set_1368_eq, calc11_set_1370_eq, calc11_set_1371_eq, calc11_set_1372_eq, calc11_set_1373_eq, calc11_set_1374_eq, calc11_finishA_1375]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1361_eq, calc11_set_1363_eq, calc11_set_1365_eq, calc11_set_1367_eq, calc11_set_1369_eq, calc11_finishT_1375]
  · decide +kernel

theorem valid_inline_850 : Valid inline_850 := by
  rw [eq_inline_850]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_452
  rcases hc with rfl | hc
  · exact placed_valid 4 (10, 0) valid_520
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 9) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_612
  subst c
  exact placed_valid 0 (2, 1) valid_633

theorem calc11_card_1376_eq : placed 5 (4, 6) card_52 = calc11_card_1376 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1377_eq : placed 7 (8, 6) card_52 = calc11_card_1377 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1378_eq : placed 1 (4, 5) card_232 = calc11_card_1378 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1379_eq : placed 3 (8, 5) card_232 = calc11_card_1379 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1380_eq : calc11_card_1379.required ∪ ∅ = calc11_set_1380 := by decide +kernel

theorem calc11_set_1381_eq : calc11_card_1379.envelope ∪ ∅ = calc11_set_1381 := by decide +kernel

theorem calc11_set_1382_eq : calc11_card_1378.required ∪ calc11_set_1380 = calc11_set_1382 := by decide +kernel

theorem calc11_set_1383_eq : calc11_card_1378.envelope ∪ calc11_set_1381 = calc11_set_1383 := by decide +kernel

theorem calc11_set_1384_eq : calc11_card_1377.required ∪ calc11_set_1382 = calc11_set_1384 := by decide +kernel

theorem calc11_set_1385_eq : calc11_card_1377.envelope ∪ calc11_set_1383 = calc11_set_1385 := by decide +kernel

theorem calc11_set_1386_eq : calc11_card_1376.required ∪ calc11_set_1384 = calc11_set_1386 := by decide +kernel

theorem calc11_set_1387_eq : calc11_card_1376.envelope ∪ calc11_set_1385 = calc11_set_1387 := by decide +kernel

theorem calc11_set_1388_eq : calc11_card_1379.envelope ∩ calc11_card_1376.envelope = calc11_set_1388 := by decide +kernel

theorem calc11_set_1389_eq : calc11_card_1378.envelope ∩ calc11_set_1388 = calc11_set_1389 := by decide +kernel

theorem calc11_set_1390_eq : calc11_card_1377.envelope ∩ calc11_set_1389 = calc11_set_1390 := by decide +kernel

theorem calc11_set_1391_eq : calc11_set_1386 ∪ calc11_set_1390 = calc11_set_1391 := by decide +kernel

theorem calc11_finishA_1392 : calc11_set_1391.erase (6, 6) = inline_851.required := by decide +kernel

theorem calc11_finishT_1392 : insert (6, 6) calc11_set_1387 = inline_851.envelope := by decide +kernel

theorem eq_inline_851 : inline_851 = combine (6, 6) [placed 5 (4, 6) card_52, placed 7 (8, 6) card_52, placed 1 (4, 5) card_232, placed 3 (8, 5) card_232] := by
  rw [calc11_card_1376_eq, calc11_card_1377_eq, calc11_card_1378_eq, calc11_card_1379_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1380_eq, calc11_set_1382_eq, calc11_set_1384_eq, calc11_set_1386_eq, calc11_set_1388_eq, calc11_set_1389_eq, calc11_set_1390_eq, calc11_set_1391_eq, calc11_finishA_1392]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1381_eq, calc11_set_1383_eq, calc11_set_1385_eq, calc11_set_1387_eq, calc11_finishT_1392]
  · decide +kernel

theorem valid_inline_851 : Valid inline_851 := by
  rw [eq_inline_851]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 5) valid_232
  subst c
  exact placed_valid 3 (8, 5) valid_232

theorem calc11_card_1393_eq : placed 5 (6, 6) card_8 = calc11_card_1393 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1394_eq : placed 3 (9, 3) card_229 = calc11_card_1394 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1395_eq : calc11_card_1394.required ∪ ∅ = calc11_set_1395 := by decide +kernel

theorem calc11_set_1396_eq : calc11_card_1394.envelope ∪ ∅ = calc11_set_1396 := by decide +kernel

theorem calc11_set_1397_eq : calc11_card_1393.required ∪ calc11_set_1395 = calc11_set_1397 := by decide +kernel

theorem calc11_set_1398_eq : calc11_card_1393.envelope ∪ calc11_set_1396 = calc11_set_1398 := by decide +kernel

theorem calc11_set_1399_eq : calc11_card_1394.envelope ∩ calc11_card_1393.envelope = calc11_set_1399 := by decide +kernel

theorem calc11_set_1400_eq : calc11_set_1397 ∪ calc11_set_1399 = calc11_set_1400 := by decide +kernel

theorem calc11_finishA_1401 : calc11_set_1400.erase (7, 3) = inline_852.required := by decide +kernel

theorem calc11_finishT_1401 : insert (7, 3) calc11_set_1398 = inline_852.envelope := by decide +kernel

theorem eq_inline_852 : inline_852 = combine (7, 3) [placed 5 (6, 6) card_8, placed 3 (9, 3) card_229] := by
  rw [calc11_card_1393_eq, calc11_card_1394_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1395_eq, calc11_set_1397_eq, calc11_set_1399_eq, calc11_set_1400_eq, calc11_finishA_1401]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1396_eq, calc11_set_1398_eq, calc11_finishT_1401]
  · decide +kernel

theorem valid_inline_852 : Valid inline_852 := by
  rw [eq_inline_852]
  apply combination_rule (7, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (6, 6) valid_8
  subst c
  exact placed_valid 3 (9, 3) valid_229

theorem calc11_card_1402_eq : placed 2 (6, 8) card_12 = calc11_card_1402 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1403_eq : placed 6 (8, 8) card_12 = calc11_card_1403 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1404_eq : placed 0 (6, 2) card_12 = calc11_card_1404 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1405_eq : placed 4 (8, 3) card_377 = calc11_card_1405 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1406_eq : inline_852.required ∪ ∅ = calc11_set_1406 := by decide +kernel

theorem calc11_set_1407_eq : inline_852.envelope ∪ ∅ = calc11_set_1407 := by decide +kernel

theorem calc11_set_1408_eq : calc11_card_1405.required ∪ calc11_set_1406 = calc11_set_1408 := by decide +kernel

theorem calc11_set_1409_eq : calc11_card_1405.envelope ∪ calc11_set_1407 = calc11_set_1409 := by decide +kernel

theorem calc11_set_1410_eq : calc11_card_1404.required ∪ calc11_set_1408 = calc11_set_1410 := by decide +kernel

theorem calc11_set_1411_eq : calc11_card_1404.envelope ∪ calc11_set_1409 = calc11_set_1411 := by decide +kernel

theorem calc11_set_1412_eq : calc11_card_1403.required ∪ calc11_set_1410 = calc11_set_1412 := by decide +kernel

theorem calc11_set_1413_eq : calc11_card_1403.envelope ∪ calc11_set_1411 = calc11_set_1413 := by decide +kernel

theorem calc11_set_1414_eq : calc11_card_1402.required ∪ calc11_set_1412 = calc11_set_1414 := by decide +kernel

theorem calc11_set_1415_eq : calc11_card_1402.envelope ∪ calc11_set_1413 = calc11_set_1415 := by decide +kernel

theorem calc11_set_1416_eq : inline_852.envelope ∩ calc11_card_1402.envelope = calc11_set_1416 := by decide +kernel

theorem calc11_set_1417_eq : calc11_card_1405.envelope ∩ calc11_set_1416 = calc11_set_1417 := by decide +kernel

theorem calc11_set_1418_eq : calc11_card_1404.envelope ∩ calc11_set_1417 = calc11_set_1418 := by decide +kernel

theorem calc11_set_1419_eq : calc11_card_1403.envelope ∩ calc11_set_1418 = calc11_set_1419 := by decide +kernel

theorem calc11_set_1420_eq : calc11_set_1414 ∪ calc11_set_1419 = calc11_set_1420 := by decide +kernel

theorem calc11_finishA_1421 : calc11_set_1420.erase (7, 4) = inline_853.required := by decide +kernel

theorem calc11_finishT_1421 : insert (7, 4) calc11_set_1415 = inline_853.envelope := by decide +kernel

theorem eq_inline_853 : inline_853 = combine (7, 4) [placed 2 (6, 8) card_12, placed 6 (8, 8) card_12, placed 0 (6, 2) card_12, placed 4 (8, 3) card_377, inline_852] := by
  rw [calc11_card_1402_eq, calc11_card_1403_eq, calc11_card_1404_eq, calc11_card_1405_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1406_eq, calc11_set_1408_eq, calc11_set_1410_eq, calc11_set_1412_eq, calc11_set_1414_eq, calc11_set_1416_eq, calc11_set_1417_eq, calc11_set_1418_eq, calc11_set_1419_eq, calc11_set_1420_eq, calc11_finishA_1421]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1407_eq, calc11_set_1409_eq, calc11_set_1411_eq, calc11_set_1413_eq, calc11_set_1415_eq, calc11_finishT_1421]
  · decide +kernel

theorem valid_inline_853 : Valid inline_853 := by
  rw [eq_inline_853]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 8) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 8) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 2) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_377
  subst c
  exact valid_inline_852

theorem calc11_card_1422_eq : placed 3 (8, 5) card_315 = calc11_card_1422 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1423_eq : placed 0 (4, 2) card_317 = calc11_card_1423 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1424_eq : placed 2 (3, 9) card_640 = calc11_card_1424 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1425_eq : calc11_card_1424.required ∪ ∅ = calc11_set_1425 := by decide +kernel

theorem calc11_set_1426_eq : calc11_card_1424.envelope ∪ ∅ = calc11_set_1426 := by decide +kernel

theorem calc11_set_1427_eq : calc11_card_1423.required ∪ calc11_set_1425 = calc11_set_1427 := by decide +kernel

theorem calc11_set_1428_eq : calc11_card_1423.envelope ∪ calc11_set_1426 = calc11_set_1428 := by decide +kernel

theorem calc11_set_1429_eq : calc11_card_1422.required ∪ calc11_set_1427 = calc11_set_1429 := by decide +kernel

theorem calc11_set_1430_eq : calc11_card_1422.envelope ∪ calc11_set_1428 = calc11_set_1430 := by decide +kernel

theorem calc11_set_1431_eq : calc11_card_1424.envelope ∩ calc11_card_1422.envelope = calc11_set_1431 := by decide +kernel

theorem calc11_set_1432_eq : calc11_card_1423.envelope ∩ calc11_set_1431 = calc11_set_1432 := by decide +kernel

theorem calc11_set_1433_eq : calc11_set_1429 ∪ calc11_set_1432 = calc11_set_1433 := by decide +kernel

theorem calc11_finishA_1434 : calc11_set_1433.erase (6, 6) = inline_854.required := by decide +kernel

theorem calc11_finishT_1434 : insert (6, 6) calc11_set_1430 = inline_854.envelope := by decide +kernel

theorem eq_inline_854 : inline_854 = combine (6, 6) [placed 3 (8, 5) card_315, placed 0 (4, 2) card_317, placed 2 (3, 9) card_640] := by
  rw [calc11_card_1422_eq, calc11_card_1423_eq, calc11_card_1424_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1425_eq, calc11_set_1427_eq, calc11_set_1429_eq, calc11_set_1431_eq, calc11_set_1432_eq, calc11_set_1433_eq, calc11_finishA_1434]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1426_eq, calc11_set_1428_eq, calc11_set_1430_eq, calc11_finishT_1434]
  · decide +kernel

theorem valid_inline_854 : Valid inline_854 := by
  rw [eq_inline_854]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_315
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_317
  subst c
  exact placed_valid 2 (3, 9) valid_640

theorem calc11_card_1435_eq : placed 3 (10, 5) card_329 = calc11_card_1435 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1436_eq : placed 0 (2, 2) card_452 = calc11_card_1436 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1437_eq : placed 2 (6, 9) card_462 = calc11_card_1437 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1438_eq : inline_854.required ∪ ∅ = calc11_set_1438 := by decide +kernel

theorem calc11_set_1439_eq : inline_854.envelope ∪ ∅ = calc11_set_1439 := by decide +kernel

theorem calc11_set_1440_eq : inline_853.required ∪ calc11_set_1438 = calc11_set_1440 := by decide +kernel

theorem calc11_set_1441_eq : inline_853.envelope ∪ calc11_set_1439 = calc11_set_1441 := by decide +kernel

theorem calc11_set_1442_eq : inline_851.required ∪ calc11_set_1440 = calc11_set_1442 := by decide +kernel

theorem calc11_set_1443_eq : inline_851.envelope ∪ calc11_set_1441 = calc11_set_1443 := by decide +kernel

theorem calc11_set_1444_eq : calc11_card_1437.required ∪ calc11_set_1442 = calc11_set_1444 := by decide +kernel

theorem calc11_set_1445_eq : calc11_card_1437.envelope ∪ calc11_set_1443 = calc11_set_1445 := by decide +kernel

theorem calc11_set_1446_eq : calc11_card_1436.required ∪ calc11_set_1444 = calc11_set_1446 := by decide +kernel

theorem calc11_set_1447_eq : calc11_card_1436.envelope ∪ calc11_set_1445 = calc11_set_1447 := by decide +kernel

theorem calc11_set_1448_eq : calc11_card_1435.required ∪ calc11_set_1446 = calc11_set_1448 := by decide +kernel

theorem calc11_set_1449_eq : calc11_card_1435.envelope ∪ calc11_set_1447 = calc11_set_1449 := by decide +kernel

theorem calc11_set_1450_eq : inline_854.envelope ∩ calc11_card_1435.envelope = calc11_set_1450 := by decide +kernel

theorem calc11_set_1451_eq : inline_853.envelope ∩ calc11_set_1450 = calc11_set_1451 := by decide +kernel

theorem calc11_set_1452_eq : inline_851.envelope ∩ calc11_set_1451 = calc11_set_1452 := by decide +kernel

theorem calc11_set_1453_eq : calc11_card_1437.envelope ∩ calc11_set_1452 = calc11_set_1453 := by decide +kernel

theorem calc11_set_1454_eq : calc11_card_1436.envelope ∩ calc11_set_1453 = calc11_set_1454 := by decide +kernel

theorem calc11_set_1455_eq : calc11_set_1448 ∪ calc11_set_1454 = calc11_set_1455 := by decide +kernel

theorem calc11_finishA_1456 : calc11_set_1455.erase (7, 6) = inline_855.required := by decide +kernel

theorem calc11_finishT_1456 : insert (7, 6) calc11_set_1449 = inline_855.envelope := by decide +kernel

theorem eq_inline_855 : inline_855 = combine (7, 6) [placed 3 (10, 5) card_329, placed 0 (2, 2) card_452, placed 2 (6, 9) card_462, inline_851, inline_853, inline_854] := by
  rw [calc11_card_1435_eq, calc11_card_1436_eq, calc11_card_1437_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1438_eq, calc11_set_1440_eq, calc11_set_1442_eq, calc11_set_1444_eq, calc11_set_1446_eq, calc11_set_1448_eq, calc11_set_1450_eq, calc11_set_1451_eq, calc11_set_1452_eq, calc11_set_1453_eq, calc11_set_1454_eq, calc11_set_1455_eq, calc11_finishA_1456]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1439_eq, calc11_set_1441_eq, calc11_set_1443_eq, calc11_set_1445_eq, calc11_set_1447_eq, calc11_set_1449_eq, calc11_finishT_1456]
  · decide +kernel

theorem valid_inline_855 : Valid inline_855 := by
  rw [eq_inline_855]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 5) valid_329
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_452
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 9) valid_462
  rcases hc with rfl | hc
  · exact valid_inline_851
  rcases hc with rfl | hc
  · exact valid_inline_853
  subst c
  exact valid_inline_854

theorem calc11_card_1457_eq : placed 6 (8, 8) card_120 = calc11_card_1457 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1458_eq : placed 5 (2, 7) card_276 = calc11_card_1458 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1459_eq : placed 5 (2, 7) card_338 = calc11_card_1459 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1460_eq : placed 5 (2, 8) card_437 = calc11_card_1460 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1461_eq : placed 5 (1, 7) card_611 = calc11_card_1461 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1462_eq : placed 0 (4, 1) card_642 = calc11_card_1462 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1463_eq : placed 0 (4, 1) card_643 = calc11_card_1463 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1464_eq : inline_855.required ∪ ∅ = calc11_set_1464 := by decide +kernel

theorem calc11_set_1465_eq : inline_855.envelope ∪ ∅ = calc11_set_1465 := by decide +kernel

theorem calc11_set_1466_eq : inline_850.required ∪ calc11_set_1464 = calc11_set_1466 := by decide +kernel

theorem calc11_set_1467_eq : inline_850.envelope ∪ calc11_set_1465 = calc11_set_1467 := by decide +kernel

theorem calc11_set_1468_eq : inline_849.required ∪ calc11_set_1466 = calc11_set_1468 := by decide +kernel

theorem calc11_set_1469_eq : inline_849.envelope ∪ calc11_set_1467 = calc11_set_1469 := by decide +kernel

theorem calc11_set_1470_eq : calc11_card_1463.required ∪ calc11_set_1468 = calc11_set_1470 := by decide +kernel

theorem calc11_set_1471_eq : calc11_card_1463.envelope ∪ calc11_set_1469 = calc11_set_1471 := by decide +kernel

theorem calc11_set_1472_eq : calc11_card_1462.required ∪ calc11_set_1470 = calc11_set_1472 := by decide +kernel

theorem calc11_set_1473_eq : calc11_card_1462.envelope ∪ calc11_set_1471 = calc11_set_1473 := by decide +kernel

theorem calc11_set_1474_eq : calc11_card_1461.required ∪ calc11_set_1472 = calc11_set_1474 := by decide +kernel

theorem calc11_set_1475_eq : calc11_card_1461.envelope ∪ calc11_set_1473 = calc11_set_1475 := by decide +kernel

theorem calc11_set_1476_eq : calc11_card_1460.required ∪ calc11_set_1474 = calc11_set_1476 := by decide +kernel

theorem calc11_set_1477_eq : calc11_card_1460.envelope ∪ calc11_set_1475 = calc11_set_1477 := by decide +kernel

theorem calc11_set_1478_eq : calc11_card_1459.required ∪ calc11_set_1476 = calc11_set_1478 := by decide +kernel

theorem calc11_set_1479_eq : calc11_card_1459.envelope ∪ calc11_set_1477 = calc11_set_1479 := by decide +kernel

theorem calc11_set_1480_eq : calc11_card_1458.required ∪ calc11_set_1478 = calc11_set_1480 := by decide +kernel

theorem calc11_set_1481_eq : calc11_card_1458.envelope ∪ calc11_set_1479 = calc11_set_1481 := by decide +kernel

theorem calc11_set_1482_eq : calc11_card_1457.required ∪ calc11_set_1480 = calc11_set_1482 := by decide +kernel

theorem calc11_set_1483_eq : calc11_card_1457.envelope ∪ calc11_set_1481 = calc11_set_1483 := by decide +kernel

theorem calc11_set_1484_eq : inline_855.envelope ∩ calc11_card_1457.envelope = calc11_set_1484 := by decide +kernel

theorem calc11_set_1485_eq : inline_850.envelope ∩ calc11_set_1484 = calc11_set_1485 := by decide +kernel

theorem calc11_set_1486_eq : inline_849.envelope ∩ calc11_set_1485 = calc11_set_1486 := by decide +kernel

theorem calc11_set_1487_eq : calc11_card_1463.envelope ∩ calc11_set_1486 = calc11_set_1487 := by decide +kernel

theorem calc11_set_1488_eq : calc11_card_1462.envelope ∩ calc11_set_1487 = calc11_set_1488 := by decide +kernel

theorem calc11_set_1489_eq : calc11_card_1461.envelope ∩ calc11_set_1488 = calc11_set_1489 := by decide +kernel

theorem calc11_set_1490_eq : calc11_card_1460.envelope ∩ calc11_set_1489 = calc11_set_1490 := by decide +kernel

theorem calc11_set_1491_eq : calc11_card_1459.envelope ∩ calc11_set_1490 = calc11_set_1491 := by decide +kernel

theorem calc11_set_1492_eq : calc11_card_1458.envelope ∩ calc11_set_1491 = calc11_set_1492 := by decide +kernel

theorem calc11_set_1493_eq : calc11_set_1482 ∪ calc11_set_1492 = calc11_set_1493 := by decide +kernel

theorem calc11_finishA_1494 : calc11_set_1493.erase (7, 5) = card_718.required := by decide +kernel

theorem calc11_finishT_1494 : insert (7, 5) calc11_set_1483 = card_718.envelope := by decide +kernel

theorem eq_card_718 : card_718 = combine (7, 5) [placed 6 (8, 8) card_120, placed 5 (2, 7) card_276, placed 5 (2, 7) card_338, placed 5 (2, 8) card_437, placed 5 (1, 7) card_611, placed 0 (4, 1) card_642, placed 0 (4, 1) card_643, inline_849, inline_850, inline_855] := by
  rw [calc11_card_1457_eq, calc11_card_1458_eq, calc11_card_1459_eq, calc11_card_1460_eq, calc11_card_1461_eq, calc11_card_1462_eq, calc11_card_1463_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1464_eq, calc11_set_1466_eq, calc11_set_1468_eq, calc11_set_1470_eq, calc11_set_1472_eq, calc11_set_1474_eq, calc11_set_1476_eq, calc11_set_1478_eq, calc11_set_1480_eq, calc11_set_1482_eq, calc11_set_1484_eq, calc11_set_1485_eq, calc11_set_1486_eq, calc11_set_1487_eq, calc11_set_1488_eq, calc11_set_1489_eq, calc11_set_1490_eq, calc11_set_1491_eq, calc11_set_1492_eq, calc11_set_1493_eq, calc11_finishA_1494]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1465_eq, calc11_set_1467_eq, calc11_set_1469_eq, calc11_set_1471_eq, calc11_set_1473_eq, calc11_set_1475_eq, calc11_set_1477_eq, calc11_set_1479_eq, calc11_set_1481_eq, calc11_set_1483_eq, calc11_finishT_1494]
  · decide +kernel

theorem valid_718 : Valid card_718 := by
  rw [eq_card_718]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 8) valid_120
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_276
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_338
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_437
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_611
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_642
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_643
  rcases hc with rfl | hc
  · exact valid_inline_849
  rcases hc with rfl | hc
  · exact valid_inline_850
  subst c
  exact valid_inline_855

theorem calc11_card_1495_eq : placed 3 (4, 5) card_5 = calc11_card_1495 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1496_eq : placed 0 (3, 4) card_412 = calc11_card_1496 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1497_eq : calc11_card_1496.required ∪ ∅ = calc11_set_1497 := by decide +kernel

theorem calc11_set_1498_eq : calc11_card_1496.envelope ∪ ∅ = calc11_set_1498 := by decide +kernel

theorem calc11_set_1499_eq : calc11_card_1495.required ∪ calc11_set_1497 = calc11_set_1499 := by decide +kernel

theorem calc11_set_1500_eq : calc11_card_1495.envelope ∪ calc11_set_1498 = calc11_set_1500 := by decide +kernel

theorem calc11_set_1501_eq : calc11_card_1496.envelope ∩ calc11_card_1495.envelope = calc11_set_1501 := by decide +kernel

theorem calc11_set_1502_eq : calc11_set_1499 ∪ calc11_set_1501 = calc11_set_1502 := by decide +kernel

theorem calc11_finishA_1503 : calc11_set_1502.erase (3, 8) = inline_856.required := by decide +kernel

theorem calc11_finishT_1503 : insert (3, 8) calc11_set_1500 = inline_856.envelope := by decide +kernel

theorem eq_inline_856 : inline_856 = combine (3, 8) [placed 3 (4, 5) card_5, placed 0 (3, 4) card_412] := by
  rw [calc11_card_1495_eq, calc11_card_1496_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1497_eq, calc11_set_1499_eq, calc11_set_1501_eq, calc11_set_1502_eq, calc11_finishA_1503]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1498_eq, calc11_set_1500_eq, calc11_finishT_1503]
  · decide +kernel

theorem valid_inline_856 : Valid inline_856 := by
  rw [eq_inline_856]
  apply combination_rule (3, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 5) valid_5
  subst c
  exact placed_valid 0 (3, 4) valid_412

theorem calc11_card_1504_eq : placed 5 (2, 8) card_45 = calc11_card_1504 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1505_eq : placed 3 (6, 5) card_343 = calc11_card_1505 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1506_eq : inline_856.required ∪ ∅ = calc11_set_1506 := by decide +kernel

theorem calc11_set_1507_eq : inline_856.envelope ∪ ∅ = calc11_set_1507 := by decide +kernel

theorem calc11_set_1508_eq : calc11_card_1505.required ∪ calc11_set_1506 = calc11_set_1508 := by decide +kernel

theorem calc11_set_1509_eq : calc11_card_1505.envelope ∪ calc11_set_1507 = calc11_set_1509 := by decide +kernel

theorem calc11_set_1510_eq : calc11_card_1504.required ∪ calc11_set_1508 = calc11_set_1510 := by decide +kernel

theorem calc11_set_1511_eq : calc11_card_1504.envelope ∪ calc11_set_1509 = calc11_set_1511 := by decide +kernel

theorem calc11_set_1512_eq : inline_856.envelope ∩ calc11_card_1504.envelope = calc11_set_1512 := by decide +kernel

theorem calc11_set_1513_eq : calc11_card_1505.envelope ∩ calc11_set_1512 = calc11_set_1513 := by decide +kernel

theorem calc11_set_1514_eq : calc11_set_1510 ∪ calc11_set_1513 = calc11_set_1514 := by decide +kernel

theorem calc11_finishA_1515 : calc11_set_1514.erase (4, 5) = inline_857.required := by decide +kernel

theorem calc11_finishT_1515 : insert (4, 5) calc11_set_1511 = inline_857.envelope := by decide +kernel

theorem eq_inline_857 : inline_857 = combine (4, 5) [placed 5 (2, 8) card_45, placed 3 (6, 5) card_343, inline_856] := by
  rw [calc11_card_1504_eq, calc11_card_1505_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1506_eq, calc11_set_1508_eq, calc11_set_1510_eq, calc11_set_1512_eq, calc11_set_1513_eq, calc11_set_1514_eq, calc11_finishA_1515]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1507_eq, calc11_set_1509_eq, calc11_set_1511_eq, calc11_finishT_1515]
  · decide +kernel

theorem valid_inline_857 : Valid inline_857 := by
  rw [eq_inline_857]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_45
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 5) valid_343
  subst c
  exact valid_inline_856

theorem calc11_card_1516_eq : placed 7 (4, 9) card_0 = calc11_card_1516 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1517_eq : inline_857.required ∪ ∅ = calc11_set_1517 := by decide +kernel

theorem calc11_set_1518_eq : inline_857.envelope ∪ ∅ = calc11_set_1518 := by decide +kernel

theorem calc11_set_1519_eq : calc11_card_1516.required ∪ calc11_set_1517 = calc11_set_1519 := by decide +kernel

theorem calc11_set_1520_eq : calc11_card_1516.envelope ∪ calc11_set_1518 = calc11_set_1520 := by decide +kernel

theorem calc11_set_1521_eq : inline_857.envelope ∩ calc11_card_1516.envelope = calc11_set_1521 := by decide +kernel

theorem calc11_set_1522_eq : calc11_set_1519 ∪ calc11_set_1521 = calc11_set_1522 := by decide +kernel

theorem calc11_finishA_1523 : calc11_set_1522.erase (4, 8) = inline_858.required := by decide +kernel

theorem calc11_finishT_1523 : insert (4, 8) calc11_set_1520 = inline_858.envelope := by decide +kernel

theorem eq_inline_858 : inline_858 = combine (4, 8) [placed 7 (4, 9) card_0, inline_857] := by
  rw [calc11_card_1516_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1517_eq, calc11_set_1519_eq, calc11_set_1521_eq, calc11_set_1522_eq, calc11_finishA_1523]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1518_eq, calc11_set_1520_eq, calc11_finishT_1523]
  · decide +kernel

theorem valid_inline_858 : Valid inline_858 := by
  rw [eq_inline_858]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 9) valid_0
  subst c
  exact valid_inline_857

theorem calc11_card_1524_eq : placed 1 (3, 3) card_1 = calc11_card_1524 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1525_eq : inline_858.required ∪ ∅ = calc11_set_1525 := by decide +kernel

theorem calc11_set_1526_eq : inline_858.envelope ∪ ∅ = calc11_set_1526 := by decide +kernel

theorem calc11_set_1527_eq : calc11_card_1524.required ∪ calc11_set_1525 = calc11_set_1527 := by decide +kernel

theorem calc11_set_1528_eq : calc11_card_1524.envelope ∪ calc11_set_1526 = calc11_set_1528 := by decide +kernel

theorem calc11_set_1529_eq : inline_858.envelope ∩ calc11_card_1524.envelope = calc11_set_1529 := by decide +kernel

theorem calc11_set_1530_eq : calc11_set_1527 ∪ calc11_set_1529 = calc11_set_1530 := by decide +kernel

theorem calc11_finishA_1531 : calc11_set_1530.erase (4, 7) = inline_859.required := by decide +kernel

theorem calc11_finishT_1531 : insert (4, 7) calc11_set_1528 = inline_859.envelope := by decide +kernel

theorem eq_inline_859 : inline_859 = combine (4, 7) [placed 1 (3, 3) card_1, inline_858] := by
  rw [calc11_card_1524_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1525_eq, calc11_set_1527_eq, calc11_set_1529_eq, calc11_set_1530_eq, calc11_finishA_1531]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1526_eq, calc11_set_1528_eq, calc11_finishT_1531]
  · decide +kernel

theorem valid_inline_859 : Valid inline_859 := by
  rw [eq_inline_859]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_1
  subst c
  exact valid_inline_858

theorem calc11_card_1532_eq : placed 1 (0, 5) card_53 = calc11_card_1532 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1533_eq : placed 7 (6, 6) card_53 = calc11_card_1533 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1534_eq : placed 7 (5, 6) card_209 = calc11_card_1534 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1535_eq : inline_859.required ∪ ∅ = calc11_set_1535 := by decide +kernel

theorem calc11_set_1536_eq : inline_859.envelope ∪ ∅ = calc11_set_1536 := by decide +kernel

theorem calc11_set_1537_eq : calc11_card_1534.required ∪ calc11_set_1535 = calc11_set_1537 := by decide +kernel

theorem calc11_set_1538_eq : calc11_card_1534.envelope ∪ calc11_set_1536 = calc11_set_1538 := by decide +kernel

theorem calc11_set_1539_eq : calc11_card_1533.required ∪ calc11_set_1537 = calc11_set_1539 := by decide +kernel

theorem calc11_set_1540_eq : calc11_card_1533.envelope ∪ calc11_set_1538 = calc11_set_1540 := by decide +kernel

theorem calc11_set_1541_eq : calc11_card_1532.required ∪ calc11_set_1539 = calc11_set_1541 := by decide +kernel

theorem calc11_set_1542_eq : calc11_card_1532.envelope ∪ calc11_set_1540 = calc11_set_1542 := by decide +kernel

theorem calc11_set_1543_eq : inline_859.envelope ∩ calc11_card_1532.envelope = calc11_set_1543 := by decide +kernel

theorem calc11_set_1544_eq : calc11_card_1534.envelope ∩ calc11_set_1543 = calc11_set_1544 := by decide +kernel

theorem calc11_set_1545_eq : calc11_card_1533.envelope ∩ calc11_set_1544 = calc11_set_1545 := by decide +kernel

theorem calc11_set_1546_eq : calc11_set_1541 ∪ calc11_set_1545 = calc11_set_1546 := by decide +kernel

theorem calc11_finishA_1547 : calc11_set_1546.erase (4, 6) = inline_860.required := by decide +kernel

theorem calc11_finishT_1547 : insert (4, 6) calc11_set_1542 = inline_860.envelope := by decide +kernel

theorem eq_inline_860 : inline_860 = combine (4, 6) [placed 1 (0, 5) card_53, placed 7 (6, 6) card_53, placed 7 (5, 6) card_209, inline_859] := by
  rw [calc11_card_1532_eq, calc11_card_1533_eq, calc11_card_1534_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1535_eq, calc11_set_1537_eq, calc11_set_1539_eq, calc11_set_1541_eq, calc11_set_1543_eq, calc11_set_1544_eq, calc11_set_1545_eq, calc11_set_1546_eq, calc11_finishA_1547]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1536_eq, calc11_set_1538_eq, calc11_set_1540_eq, calc11_set_1542_eq, calc11_finishT_1547]
  · decide +kernel

theorem valid_inline_860 : Valid inline_860 := by
  rw [eq_inline_860]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 5) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_209
  subst c
  exact valid_inline_859

theorem calc11_card_1548_eq : placed 0 (2, 2) card_53 = calc11_card_1548 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1549_eq : placed 6 (3, 8) card_53 = calc11_card_1549 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1550_eq : placed 6 (3, 7) card_209 = calc11_card_1550 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1551_eq : inline_860.required ∪ ∅ = calc11_set_1551 := by decide +kernel

theorem calc11_set_1552_eq : inline_860.envelope ∪ ∅ = calc11_set_1552 := by decide +kernel

theorem calc11_set_1553_eq : calc11_card_1550.required ∪ calc11_set_1551 = calc11_set_1553 := by decide +kernel

theorem calc11_set_1554_eq : calc11_card_1550.envelope ∪ calc11_set_1552 = calc11_set_1554 := by decide +kernel

theorem calc11_set_1555_eq : calc11_card_1549.required ∪ calc11_set_1553 = calc11_set_1555 := by decide +kernel

theorem calc11_set_1556_eq : calc11_card_1549.envelope ∪ calc11_set_1554 = calc11_set_1556 := by decide +kernel

theorem calc11_set_1557_eq : calc11_card_1548.required ∪ calc11_set_1555 = calc11_set_1557 := by decide +kernel

theorem calc11_set_1558_eq : calc11_card_1548.envelope ∪ calc11_set_1556 = calc11_set_1558 := by decide +kernel

theorem calc11_set_1559_eq : inline_860.envelope ∩ calc11_card_1548.envelope = calc11_set_1559 := by decide +kernel

theorem calc11_set_1560_eq : calc11_card_1550.envelope ∩ calc11_set_1559 = calc11_set_1560 := by decide +kernel

theorem calc11_set_1561_eq : calc11_card_1549.envelope ∩ calc11_set_1560 = calc11_set_1561 := by decide +kernel

theorem calc11_set_1562_eq : calc11_set_1557 ∪ calc11_set_1561 = calc11_set_1562 := by decide +kernel

theorem calc11_finishA_1563 : calc11_set_1562.erase (3, 6) = inline_861.required := by decide +kernel

theorem calc11_finishT_1563 : insert (3, 6) calc11_set_1558 = inline_861.envelope := by decide +kernel

theorem eq_inline_861 : inline_861 = combine (3, 6) [placed 0 (2, 2) card_53, placed 6 (3, 8) card_53, placed 6 (3, 7) card_209, inline_860] := by
  rw [calc11_card_1548_eq, calc11_card_1549_eq, calc11_card_1550_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1551_eq, calc11_set_1553_eq, calc11_set_1555_eq, calc11_set_1557_eq, calc11_set_1559_eq, calc11_set_1560_eq, calc11_set_1561_eq, calc11_set_1562_eq, calc11_finishA_1563]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1552_eq, calc11_set_1554_eq, calc11_set_1556_eq, calc11_set_1558_eq, calc11_finishT_1563]
  · decide +kernel

theorem valid_inline_861 : Valid inline_861 := by
  rw [eq_inline_861]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 8) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 7) valid_209
  subst c
  exact valid_inline_860

theorem calc11_card_1564_eq : placed 0 (2, 1) card_65 = calc11_card_1564 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1565_eq : placed 1 (0, 3) card_301 = calc11_card_1565 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1566_eq : placed 7 (5, 5) card_417 = calc11_card_1566 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1567_eq : calc11_card_1566.required ∪ ∅ = calc11_set_1567 := by decide +kernel

theorem calc11_set_1568_eq : calc11_card_1566.envelope ∪ ∅ = calc11_set_1568 := by decide +kernel

theorem calc11_set_1569_eq : calc11_card_1565.required ∪ calc11_set_1567 = calc11_set_1569 := by decide +kernel

theorem calc11_set_1570_eq : calc11_card_1565.envelope ∪ calc11_set_1568 = calc11_set_1570 := by decide +kernel

theorem calc11_set_1571_eq : calc11_card_1564.required ∪ calc11_set_1569 = calc11_set_1571 := by decide +kernel

theorem calc11_set_1572_eq : calc11_card_1564.envelope ∪ calc11_set_1570 = calc11_set_1572 := by decide +kernel

theorem calc11_set_1573_eq : calc11_card_1566.envelope ∩ calc11_card_1564.envelope = calc11_set_1573 := by decide +kernel

theorem calc11_set_1574_eq : calc11_card_1565.envelope ∩ calc11_set_1573 = calc11_set_1574 := by decide +kernel

theorem calc11_set_1575_eq : calc11_set_1571 ∪ calc11_set_1574 = calc11_set_1575 := by decide +kernel

theorem calc11_finishA_1576 : calc11_set_1575.erase (3, 4) = inline_862.required := by decide +kernel

theorem calc11_finishT_1576 : insert (3, 4) calc11_set_1572 = inline_862.envelope := by decide +kernel

theorem eq_inline_862 : inline_862 = combine (3, 4) [placed 0 (2, 1) card_65, placed 1 (0, 3) card_301, placed 7 (5, 5) card_417] := by
  rw [calc11_card_1564_eq, calc11_card_1565_eq, calc11_card_1566_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1567_eq, calc11_set_1569_eq, calc11_set_1571_eq, calc11_set_1573_eq, calc11_set_1574_eq, calc11_set_1575_eq, calc11_finishA_1576]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1568_eq, calc11_set_1570_eq, calc11_set_1572_eq, calc11_finishT_1576]
  · decide +kernel

theorem valid_inline_862 : Valid inline_862 := by
  rw [eq_inline_862]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_65
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_301
  subst c
  exact placed_valid 7 (5, 5) valid_417

theorem calc11_card_1577_eq : placed 4 (3, 2) card_15 = calc11_card_1577 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1578_eq : placed 0 (2, 1) card_65 = calc11_card_1578 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1579_eq : placed 1 (1, 3) card_72 = calc11_card_1579 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1580_eq : calc11_card_1579.required ∪ ∅ = calc11_set_1580 := by decide +kernel

theorem calc11_set_1581_eq : calc11_card_1579.envelope ∪ ∅ = calc11_set_1581 := by decide +kernel

theorem calc11_set_1582_eq : calc11_card_1578.required ∪ calc11_set_1580 = calc11_set_1582 := by decide +kernel

theorem calc11_set_1583_eq : calc11_card_1578.envelope ∪ calc11_set_1581 = calc11_set_1583 := by decide +kernel

theorem calc11_set_1584_eq : calc11_card_1577.required ∪ calc11_set_1582 = calc11_set_1584 := by decide +kernel

theorem calc11_set_1585_eq : calc11_card_1577.envelope ∪ calc11_set_1583 = calc11_set_1585 := by decide +kernel

theorem calc11_set_1586_eq : calc11_card_1579.envelope ∩ calc11_card_1577.envelope = calc11_set_1586 := by decide +kernel

theorem calc11_set_1587_eq : calc11_card_1578.envelope ∩ calc11_set_1586 = calc11_set_1587 := by decide +kernel

theorem calc11_set_1588_eq : calc11_set_1584 ∪ calc11_set_1587 = calc11_set_1588 := by decide +kernel

theorem calc11_finishA_1589 : calc11_set_1588.erase (3, 4) = inline_863.required := by decide +kernel

theorem calc11_finishT_1589 : insert (3, 4) calc11_set_1585 = inline_863.envelope := by decide +kernel

theorem eq_inline_863 : inline_863 = combine (3, 4) [placed 4 (3, 2) card_15, placed 0 (2, 1) card_65, placed 1 (1, 3) card_72] := by
  rw [calc11_card_1577_eq, calc11_card_1578_eq, calc11_card_1579_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1580_eq, calc11_set_1582_eq, calc11_set_1584_eq, calc11_set_1586_eq, calc11_set_1587_eq, calc11_set_1588_eq, calc11_finishA_1589]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1581_eq, calc11_set_1583_eq, calc11_set_1585_eq, calc11_finishT_1589]
  · decide +kernel

theorem valid_inline_863 : Valid inline_863 := by
  rw [eq_inline_863]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_65
  subst c
  exact placed_valid 1 (1, 3) valid_72

theorem calc11_card_1590_eq : placed 4 (3, 0) card_318 = calc11_card_1590 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1591_eq : placed 2 (2, 7) card_334 = calc11_card_1591 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1592_eq : inline_863.required ∪ ∅ = calc11_set_1592 := by decide +kernel

theorem calc11_set_1593_eq : inline_863.envelope ∪ ∅ = calc11_set_1593 := by decide +kernel

theorem calc11_set_1594_eq : inline_862.required ∪ calc11_set_1592 = calc11_set_1594 := by decide +kernel

theorem calc11_set_1595_eq : inline_862.envelope ∪ calc11_set_1593 = calc11_set_1595 := by decide +kernel

theorem calc11_set_1596_eq : inline_861.required ∪ calc11_set_1594 = calc11_set_1596 := by decide +kernel

theorem calc11_set_1597_eq : inline_861.envelope ∪ calc11_set_1595 = calc11_set_1597 := by decide +kernel

theorem calc11_set_1598_eq : calc11_card_1591.required ∪ calc11_set_1596 = calc11_set_1598 := by decide +kernel

theorem calc11_set_1599_eq : calc11_card_1591.envelope ∪ calc11_set_1597 = calc11_set_1599 := by decide +kernel

theorem calc11_set_1600_eq : calc11_card_1590.required ∪ calc11_set_1598 = calc11_set_1600 := by decide +kernel

theorem calc11_set_1601_eq : calc11_card_1590.envelope ∪ calc11_set_1599 = calc11_set_1601 := by decide +kernel

theorem calc11_set_1602_eq : inline_863.envelope ∩ calc11_card_1590.envelope = calc11_set_1602 := by decide +kernel

theorem calc11_set_1603_eq : inline_862.envelope ∩ calc11_set_1602 = calc11_set_1603 := by decide +kernel

theorem calc11_set_1604_eq : inline_861.envelope ∩ calc11_set_1603 = calc11_set_1604 := by decide +kernel

theorem calc11_set_1605_eq : calc11_card_1591.envelope ∩ calc11_set_1604 = calc11_set_1605 := by decide +kernel

theorem calc11_set_1606_eq : calc11_set_1600 ∪ calc11_set_1605 = calc11_set_1606 := by decide +kernel

theorem calc11_finishA_1607 : calc11_set_1606.erase (3, 3) = card_719.required := by decide +kernel

theorem calc11_finishT_1607 : insert (3, 3) calc11_set_1601 = card_719.envelope := by decide +kernel

theorem eq_card_719 : card_719 = combine (3, 3) [placed 4 (3, 0) card_318, placed 2 (2, 7) card_334, inline_861, inline_862, inline_863] := by
  rw [calc11_card_1590_eq, calc11_card_1591_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1592_eq, calc11_set_1594_eq, calc11_set_1596_eq, calc11_set_1598_eq, calc11_set_1600_eq, calc11_set_1602_eq, calc11_set_1603_eq, calc11_set_1604_eq, calc11_set_1605_eq, calc11_set_1606_eq, calc11_finishA_1607]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1593_eq, calc11_set_1595_eq, calc11_set_1597_eq, calc11_set_1599_eq, calc11_set_1601_eq, calc11_finishT_1607]
  · decide +kernel

theorem valid_719 : Valid card_719 := by
  rw [eq_card_719]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_318
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_334
  rcases hc with rfl | hc
  · exact valid_inline_861
  rcases hc with rfl | hc
  · exact valid_inline_862
  subst c
  exact valid_inline_863

theorem calc11_card_1608_eq : placed 7 (6, 6) card_10 = calc11_card_1608 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1609_eq : placed 4 (6, 3) card_180 = calc11_card_1609 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1610_eq : placed 1 (3, 5) card_200 = calc11_card_1610 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1611_eq : calc11_card_1610.required ∪ ∅ = calc11_set_1611 := by decide +kernel

theorem calc11_set_1612_eq : calc11_card_1610.envelope ∪ ∅ = calc11_set_1612 := by decide +kernel

theorem calc11_set_1613_eq : calc11_card_1609.required ∪ calc11_set_1611 = calc11_set_1613 := by decide +kernel

theorem calc11_set_1614_eq : calc11_card_1609.envelope ∪ calc11_set_1612 = calc11_set_1614 := by decide +kernel

theorem calc11_set_1615_eq : calc11_card_1608.required ∪ calc11_set_1613 = calc11_set_1615 := by decide +kernel

theorem calc11_set_1616_eq : calc11_card_1608.envelope ∪ calc11_set_1614 = calc11_set_1616 := by decide +kernel

theorem calc11_set_1617_eq : calc11_card_1610.envelope ∩ calc11_card_1608.envelope = calc11_set_1617 := by decide +kernel

theorem calc11_set_1618_eq : calc11_card_1609.envelope ∩ calc11_set_1617 = calc11_set_1618 := by decide +kernel

theorem calc11_set_1619_eq : calc11_set_1615 ∪ calc11_set_1618 = calc11_set_1619 := by decide +kernel

theorem calc11_finishA_1620 : calc11_set_1619.erase (3, 5) = inline_864.required := by decide +kernel

theorem calc11_finishT_1620 : insert (3, 5) calc11_set_1616 = inline_864.envelope := by decide +kernel

theorem eq_inline_864 : inline_864 = combine (3, 5) [placed 7 (6, 6) card_10, placed 4 (6, 3) card_180, placed 1 (3, 5) card_200] := by
  rw [calc11_card_1608_eq, calc11_card_1609_eq, calc11_card_1610_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1611_eq, calc11_set_1613_eq, calc11_set_1615_eq, calc11_set_1617_eq, calc11_set_1618_eq, calc11_set_1619_eq, calc11_finishA_1620]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1612_eq, calc11_set_1614_eq, calc11_set_1616_eq, calc11_finishT_1620]
  · decide +kernel

theorem valid_inline_864 : Valid inline_864 := by
  rw [eq_inline_864]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_180
  subst c
  exact placed_valid 1 (3, 5) valid_200

theorem calc11_card_1621_eq : placed 4 (7, 4) card_52 = calc11_card_1621 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1622_eq : placed 1 (4, 6) card_315 = calc11_card_1622 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1623_eq : calc11_card_1622.required ∪ ∅ = calc11_set_1623 := by decide +kernel

theorem calc11_set_1624_eq : calc11_card_1622.envelope ∪ ∅ = calc11_set_1624 := by decide +kernel

theorem calc11_set_1625_eq : calc11_card_1621.required ∪ calc11_set_1623 = calc11_set_1625 := by decide +kernel

theorem calc11_set_1626_eq : calc11_card_1621.envelope ∪ calc11_set_1624 = calc11_set_1626 := by decide +kernel

theorem calc11_set_1627_eq : calc11_card_1622.envelope ∩ calc11_card_1621.envelope = calc11_set_1627 := by decide +kernel

theorem calc11_set_1628_eq : calc11_set_1625 ∪ calc11_set_1627 = calc11_set_1628 := by decide +kernel

theorem calc11_finishA_1629 : calc11_set_1628.erase (6, 7) = inline_865.required := by decide +kernel

theorem calc11_finishT_1629 : insert (6, 7) calc11_set_1626 = inline_865.envelope := by decide +kernel

theorem eq_inline_865 : inline_865 = combine (6, 7) [placed 4 (7, 4) card_52, placed 1 (4, 6) card_315] := by
  rw [calc11_card_1621_eq, calc11_card_1622_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1623_eq, calc11_set_1625_eq, calc11_set_1627_eq, calc11_set_1628_eq, calc11_finishA_1629]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1624_eq, calc11_set_1626_eq, calc11_finishT_1629]
  · decide +kernel

theorem valid_inline_865 : Valid inline_865 := by
  rw [eq_inline_865]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 4) valid_52
  subst c
  exact placed_valid 1 (4, 6) valid_315

theorem calc11_card_1630_eq : placed 7 (8, 7) card_197 = calc11_card_1630 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1631_eq : placed 3 (8, 4) card_201 = calc11_card_1631 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1632_eq : calc11_card_1631.required ∪ ∅ = calc11_set_1632 := by decide +kernel

theorem calc11_set_1633_eq : calc11_card_1631.envelope ∪ ∅ = calc11_set_1633 := by decide +kernel

theorem calc11_set_1634_eq : calc11_card_1630.required ∪ calc11_set_1632 = calc11_set_1634 := by decide +kernel

theorem calc11_set_1635_eq : calc11_card_1630.envelope ∪ calc11_set_1633 = calc11_set_1635 := by decide +kernel

theorem calc11_set_1636_eq : calc11_card_1631.envelope ∩ calc11_card_1630.envelope = calc11_set_1636 := by decide +kernel

theorem calc11_set_1637_eq : calc11_set_1634 ∪ calc11_set_1636 = calc11_set_1637 := by decide +kernel

theorem calc11_finishA_1638 : calc11_set_1637.erase (7, 4) = inline_866.required := by decide +kernel

theorem calc11_finishT_1638 : insert (7, 4) calc11_set_1635 = inline_866.envelope := by decide +kernel

theorem eq_inline_866 : inline_866 = combine (7, 4) [placed 7 (8, 7) card_197, placed 3 (8, 4) card_201] := by
  rw [calc11_card_1630_eq, calc11_card_1631_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1632_eq, calc11_set_1634_eq, calc11_set_1636_eq, calc11_set_1637_eq, calc11_finishA_1638]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1633_eq, calc11_set_1635_eq, calc11_finishT_1638]
  · decide +kernel

theorem valid_inline_866 : Valid inline_866 := by
  rw [eq_inline_866]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 7) valid_197
  subst c
  exact placed_valid 3 (8, 4) valid_201

theorem calc11_card_1639_eq : placed 4 (8, 3) card_12 = calc11_card_1639 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1640_eq : placed 4 (8, 3) card_13 = calc11_card_1640 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1641_eq : placed 6 (8, 10) card_369 = calc11_card_1641 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1642_eq : placed 1 (5, 4) card_474 = calc11_card_1642 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1643_eq : inline_866.required ∪ ∅ = calc11_set_1643 := by decide +kernel

theorem calc11_set_1644_eq : inline_866.envelope ∪ ∅ = calc11_set_1644 := by decide +kernel

theorem calc11_set_1645_eq : inline_865.required ∪ calc11_set_1643 = calc11_set_1645 := by decide +kernel

theorem calc11_set_1646_eq : inline_865.envelope ∪ calc11_set_1644 = calc11_set_1646 := by decide +kernel

theorem calc11_set_1647_eq : calc11_card_1642.required ∪ calc11_set_1645 = calc11_set_1647 := by decide +kernel

theorem calc11_set_1648_eq : calc11_card_1642.envelope ∪ calc11_set_1646 = calc11_set_1648 := by decide +kernel

theorem calc11_set_1649_eq : calc11_card_1641.required ∪ calc11_set_1647 = calc11_set_1649 := by decide +kernel

theorem calc11_set_1650_eq : calc11_card_1641.envelope ∪ calc11_set_1648 = calc11_set_1650 := by decide +kernel

theorem calc11_set_1651_eq : calc11_card_1640.required ∪ calc11_set_1649 = calc11_set_1651 := by decide +kernel

theorem calc11_set_1652_eq : calc11_card_1640.envelope ∪ calc11_set_1650 = calc11_set_1652 := by decide +kernel

theorem calc11_set_1653_eq : calc11_card_1639.required ∪ calc11_set_1651 = calc11_set_1653 := by decide +kernel

theorem calc11_set_1654_eq : calc11_card_1639.envelope ∪ calc11_set_1652 = calc11_set_1654 := by decide +kernel

theorem calc11_set_1655_eq : inline_866.envelope ∩ calc11_card_1639.envelope = calc11_set_1655 := by decide +kernel

theorem calc11_set_1656_eq : inline_865.envelope ∩ calc11_set_1655 = calc11_set_1656 := by decide +kernel

theorem calc11_set_1657_eq : calc11_card_1642.envelope ∩ calc11_set_1656 = calc11_set_1657 := by decide +kernel

theorem calc11_set_1658_eq : calc11_card_1641.envelope ∩ calc11_set_1657 = calc11_set_1658 := by decide +kernel

theorem calc11_set_1659_eq : calc11_card_1640.envelope ∩ calc11_set_1658 = calc11_set_1659 := by decide +kernel

theorem calc11_set_1660_eq : calc11_set_1653 ∪ calc11_set_1659 = calc11_set_1660 := by decide +kernel

theorem calc11_finishA_1661 : calc11_set_1660.erase (7, 7) = inline_867.required := by decide +kernel

theorem calc11_finishT_1661 : insert (7, 7) calc11_set_1654 = inline_867.envelope := by decide +kernel

theorem eq_inline_867 : inline_867 = combine (7, 7) [placed 4 (8, 3) card_12, placed 4 (8, 3) card_13, placed 6 (8, 10) card_369, placed 1 (5, 4) card_474, inline_865, inline_866] := by
  rw [calc11_card_1639_eq, calc11_card_1640_eq, calc11_card_1641_eq, calc11_card_1642_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1643_eq, calc11_set_1645_eq, calc11_set_1647_eq, calc11_set_1649_eq, calc11_set_1651_eq, calc11_set_1653_eq, calc11_set_1655_eq, calc11_set_1656_eq, calc11_set_1657_eq, calc11_set_1658_eq, calc11_set_1659_eq, calc11_set_1660_eq, calc11_finishA_1661]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1644_eq, calc11_set_1646_eq, calc11_set_1648_eq, calc11_set_1650_eq, calc11_set_1652_eq, calc11_set_1654_eq, calc11_finishT_1661]
  · decide +kernel

theorem valid_inline_867 : Valid inline_867 := by
  rw [eq_inline_867]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 10) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 4) valid_474
  rcases hc with rfl | hc
  · exact valid_inline_865
  subst c
  exact valid_inline_866

theorem calc11_card_1662_eq : placed 7 (5, 8) card_0 = calc11_card_1662 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1663_eq : inline_867.required ∪ ∅ = calc11_set_1663 := by decide +kernel

theorem calc11_set_1664_eq : inline_867.envelope ∪ ∅ = calc11_set_1664 := by decide +kernel

theorem calc11_set_1665_eq : calc11_card_1662.required ∪ calc11_set_1663 = calc11_set_1665 := by decide +kernel

theorem calc11_set_1666_eq : calc11_card_1662.envelope ∪ calc11_set_1664 = calc11_set_1666 := by decide +kernel

theorem calc11_set_1667_eq : inline_867.envelope ∩ calc11_card_1662.envelope = calc11_set_1667 := by decide +kernel

theorem calc11_set_1668_eq : calc11_set_1665 ∪ calc11_set_1667 = calc11_set_1668 := by decide +kernel

theorem calc11_finishA_1669 : calc11_set_1668.erase (5, 7) = inline_868.required := by decide +kernel

theorem calc11_finishT_1669 : insert (5, 7) calc11_set_1666 = inline_868.envelope := by decide +kernel

theorem eq_inline_868 : inline_868 = combine (5, 7) [placed 7 (5, 8) card_0, inline_867] := by
  rw [calc11_card_1662_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1663_eq, calc11_set_1665_eq, calc11_set_1667_eq, calc11_set_1668_eq, calc11_finishA_1669]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1664_eq, calc11_set_1666_eq, calc11_finishT_1669]
  · decide +kernel

theorem valid_inline_868 : Valid inline_868 := by
  rw [eq_inline_868]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 8) valid_0
  subst c
  exact valid_inline_867

theorem calc11_card_1670_eq : placed 1 (3, 4) card_40 = calc11_card_1670 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1671_eq : placed 1 (3, 4) card_310 = calc11_card_1671 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1672_eq : inline_868.required ∪ ∅ = calc11_set_1672 := by decide +kernel

theorem calc11_set_1673_eq : inline_868.envelope ∪ ∅ = calc11_set_1673 := by decide +kernel

theorem calc11_set_1674_eq : calc11_card_1671.required ∪ calc11_set_1672 = calc11_set_1674 := by decide +kernel

theorem calc11_set_1675_eq : calc11_card_1671.envelope ∪ calc11_set_1673 = calc11_set_1675 := by decide +kernel

theorem calc11_set_1676_eq : calc11_card_1670.required ∪ calc11_set_1674 = calc11_set_1676 := by decide +kernel

theorem calc11_set_1677_eq : calc11_card_1670.envelope ∪ calc11_set_1675 = calc11_set_1677 := by decide +kernel

theorem calc11_set_1678_eq : inline_868.envelope ∩ calc11_card_1670.envelope = calc11_set_1678 := by decide +kernel

theorem calc11_set_1679_eq : calc11_card_1671.envelope ∩ calc11_set_1678 = calc11_set_1679 := by decide +kernel

theorem calc11_set_1680_eq : calc11_set_1676 ∪ calc11_set_1679 = calc11_set_1680 := by decide +kernel

theorem calc11_finishA_1681 : calc11_set_1680.erase (7, 5) = inline_869.required := by decide +kernel

theorem calc11_finishT_1681 : insert (7, 5) calc11_set_1677 = inline_869.envelope := by decide +kernel

theorem eq_inline_869 : inline_869 = combine (7, 5) [placed 1 (3, 4) card_40, placed 1 (3, 4) card_310, inline_868] := by
  rw [calc11_card_1670_eq, calc11_card_1671_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1672_eq, calc11_set_1674_eq, calc11_set_1676_eq, calc11_set_1678_eq, calc11_set_1679_eq, calc11_set_1680_eq, calc11_finishA_1681]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1673_eq, calc11_set_1675_eq, calc11_set_1677_eq, calc11_finishT_1681]
  · decide +kernel

theorem valid_inline_869 : Valid inline_869 := by
  rw [eq_inline_869]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_310
  subst c
  exact valid_inline_868

theorem calc11_card_1682_eq : placed 7 (8, 6) card_54 = calc11_card_1682 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1683_eq : placed 7 (8, 6) card_64 = calc11_card_1683 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1684_eq : inline_869.required ∪ ∅ = calc11_set_1684 := by decide +kernel

theorem calc11_set_1685_eq : inline_869.envelope ∪ ∅ = calc11_set_1685 := by decide +kernel

theorem calc11_set_1686_eq : inline_864.required ∪ calc11_set_1684 = calc11_set_1686 := by decide +kernel

theorem calc11_set_1687_eq : inline_864.envelope ∪ calc11_set_1685 = calc11_set_1687 := by decide +kernel

theorem calc11_set_1688_eq : calc11_card_1683.required ∪ calc11_set_1686 = calc11_set_1688 := by decide +kernel

theorem calc11_set_1689_eq : calc11_card_1683.envelope ∪ calc11_set_1687 = calc11_set_1689 := by decide +kernel

theorem calc11_set_1690_eq : calc11_card_1682.required ∪ calc11_set_1688 = calc11_set_1690 := by decide +kernel

theorem calc11_set_1691_eq : calc11_card_1682.envelope ∪ calc11_set_1689 = calc11_set_1691 := by decide +kernel

theorem calc11_set_1692_eq : inline_869.envelope ∩ calc11_card_1682.envelope = calc11_set_1692 := by decide +kernel

theorem calc11_set_1693_eq : inline_864.envelope ∩ calc11_set_1692 = calc11_set_1693 := by decide +kernel

theorem calc11_set_1694_eq : calc11_card_1683.envelope ∩ calc11_set_1693 = calc11_set_1694 := by decide +kernel

theorem calc11_set_1695_eq : calc11_set_1690 ∪ calc11_set_1694 = calc11_set_1695 := by decide +kernel

theorem calc11_finishA_1696 : calc11_set_1695.erase (7, 6) = card_720.required := by decide +kernel

theorem calc11_finishT_1696 : insert (7, 6) calc11_set_1691 = card_720.envelope := by decide +kernel

theorem eq_card_720 : card_720 = combine (7, 6) [placed 7 (8, 6) card_54, placed 7 (8, 6) card_64, inline_864, inline_869] := by
  rw [calc11_card_1682_eq, calc11_card_1683_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1684_eq, calc11_set_1686_eq, calc11_set_1688_eq, calc11_set_1690_eq, calc11_set_1692_eq, calc11_set_1693_eq, calc11_set_1694_eq, calc11_set_1695_eq, calc11_finishA_1696]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1685_eq, calc11_set_1687_eq, calc11_set_1689_eq, calc11_set_1691_eq, calc11_finishT_1696]
  · decide +kernel

theorem valid_720 : Valid card_720 := by
  rw [eq_card_720]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_64
  rcases hc with rfl | hc
  · exact valid_inline_864
  subst c
  exact valid_inline_869

theorem calc11_card_1697_eq : placed 2 (2, 6) card_5 = calc11_card_1697 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1698_eq : placed 6 (5, 7) card_208 = calc11_card_1698 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1699_eq : calc11_card_1698.required ∪ ∅ = calc11_set_1699 := by decide +kernel

theorem calc11_set_1700_eq : calc11_card_1698.envelope ∪ ∅ = calc11_set_1700 := by decide +kernel

theorem calc11_set_1701_eq : calc11_card_1697.required ∪ calc11_set_1699 = calc11_set_1701 := by decide +kernel

theorem calc11_set_1702_eq : calc11_card_1697.envelope ∪ calc11_set_1700 = calc11_set_1702 := by decide +kernel

theorem calc11_set_1703_eq : calc11_card_1698.envelope ∩ calc11_card_1697.envelope = calc11_set_1703 := by decide +kernel

theorem calc11_set_1704_eq : calc11_set_1701 ∪ calc11_set_1703 = calc11_set_1704 := by decide +kernel

theorem calc11_finishA_1705 : calc11_set_1704.erase (2, 6) = inline_870.required := by decide +kernel

theorem calc11_finishT_1705 : insert (2, 6) calc11_set_1702 = inline_870.envelope := by decide +kernel

theorem eq_inline_870 : inline_870 = combine (2, 6) [placed 2 (2, 6) card_5, placed 6 (5, 7) card_208] := by
  rw [calc11_card_1697_eq, calc11_card_1698_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1699_eq, calc11_set_1701_eq, calc11_set_1703_eq, calc11_set_1704_eq, calc11_finishA_1705]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1700_eq, calc11_set_1702_eq, calc11_finishT_1705]
  · decide +kernel

theorem valid_inline_870 : Valid inline_870 := by
  rw [eq_inline_870]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_5
  subst c
  exact placed_valid 6 (5, 7) valid_208

theorem calc11_card_1706_eq : placed 3 (5, 3) card_5 = calc11_card_1706 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1707_eq : inline_870.required ∪ ∅ = calc11_set_1707 := by decide +kernel

theorem calc11_set_1708_eq : inline_870.envelope ∪ ∅ = calc11_set_1708 := by decide +kernel

theorem calc11_set_1709_eq : calc11_card_1706.required ∪ calc11_set_1707 = calc11_set_1709 := by decide +kernel

theorem calc11_set_1710_eq : calc11_card_1706.envelope ∪ calc11_set_1708 = calc11_set_1710 := by decide +kernel

theorem calc11_set_1711_eq : inline_870.envelope ∩ calc11_card_1706.envelope = calc11_set_1711 := by decide +kernel

theorem calc11_set_1712_eq : calc11_set_1709 ∪ calc11_set_1711 = calc11_set_1712 := by decide +kernel

theorem calc11_finishA_1713 : calc11_set_1712.erase (4, 6) = inline_871.required := by decide +kernel

theorem calc11_finishT_1713 : insert (4, 6) calc11_set_1710 = inline_871.envelope := by decide +kernel

theorem eq_inline_871 : inline_871 = combine (4, 6) [placed 3 (5, 3) card_5, inline_870] := by
  rw [calc11_card_1706_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1707_eq, calc11_set_1709_eq, calc11_set_1711_eq, calc11_set_1712_eq, calc11_finishA_1713]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1708_eq, calc11_set_1710_eq, calc11_finishT_1713]
  · decide +kernel

theorem valid_inline_871 : Valid inline_871 := by
  rw [eq_inline_871]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_5
  subst c
  exact valid_inline_870

theorem calc11_card_1714_eq : placed 4 (3, 2) card_22 = calc11_card_1714 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1715_eq : inline_871.required ∪ ∅ = calc11_set_1715 := by decide +kernel

theorem calc11_set_1716_eq : inline_871.envelope ∪ ∅ = calc11_set_1716 := by decide +kernel

theorem calc11_set_1717_eq : calc11_card_1714.required ∪ calc11_set_1715 = calc11_set_1717 := by decide +kernel

theorem calc11_set_1718_eq : calc11_card_1714.envelope ∪ calc11_set_1716 = calc11_set_1718 := by decide +kernel

theorem calc11_set_1719_eq : inline_871.envelope ∩ calc11_card_1714.envelope = calc11_set_1719 := by decide +kernel

theorem calc11_set_1720_eq : calc11_set_1717 ∪ calc11_set_1719 = calc11_set_1720 := by decide +kernel

theorem calc11_finishA_1721 : calc11_set_1720.erase (3, 6) = inline_872.required := by decide +kernel

theorem calc11_finishT_1721 : insert (3, 6) calc11_set_1718 = inline_872.envelope := by decide +kernel

theorem eq_inline_872 : inline_872 = combine (3, 6) [placed 4 (3, 2) card_22, inline_871] := by
  rw [calc11_card_1714_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1715_eq, calc11_set_1717_eq, calc11_set_1719_eq, calc11_set_1720_eq, calc11_finishA_1721]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1716_eq, calc11_set_1718_eq, calc11_finishT_1721]
  · decide +kernel

theorem valid_inline_872 : Valid inline_872 := by
  rw [eq_inline_872]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_22
  subst c
  exact valid_inline_871

theorem calc11_card_1722_eq : placed 7 (6, 6) card_25 = calc11_card_1722 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1723_eq : inline_872.required ∪ ∅ = calc11_set_1723 := by decide +kernel

theorem calc11_set_1724_eq : inline_872.envelope ∪ ∅ = calc11_set_1724 := by decide +kernel

theorem calc11_set_1725_eq : calc11_card_1722.required ∪ calc11_set_1723 = calc11_set_1725 := by decide +kernel

theorem calc11_set_1726_eq : calc11_card_1722.envelope ∪ calc11_set_1724 = calc11_set_1726 := by decide +kernel

theorem calc11_set_1727_eq : inline_872.envelope ∩ calc11_card_1722.envelope = calc11_set_1727 := by decide +kernel

theorem calc11_set_1728_eq : calc11_set_1725 ∪ calc11_set_1727 = calc11_set_1728 := by decide +kernel

theorem calc11_finishA_1729 : calc11_set_1728.erase (2, 4) = inline_873.required := by decide +kernel

theorem calc11_finishT_1729 : insert (2, 4) calc11_set_1726 = inline_873.envelope := by decide +kernel

theorem eq_inline_873 : inline_873 = combine (2, 4) [placed 7 (6, 6) card_25, inline_872] := by
  rw [calc11_card_1722_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1723_eq, calc11_set_1725_eq, calc11_set_1727_eq, calc11_set_1728_eq, calc11_finishA_1729]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1724_eq, calc11_set_1726_eq, calc11_finishT_1729]
  · decide +kernel

theorem valid_inline_873 : Valid inline_873 := by
  rw [eq_inline_873]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_25
  subst c
  exact valid_inline_872

theorem calc11_card_1730_eq : placed 2 (5, 7) card_7 = calc11_card_1730 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1731_eq : placed 3 (6, 3) card_8 = calc11_card_1731 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1732_eq : inline_873.required ∪ ∅ = calc11_set_1732 := by decide +kernel

theorem calc11_set_1733_eq : inline_873.envelope ∪ ∅ = calc11_set_1733 := by decide +kernel

theorem calc11_set_1734_eq : calc11_card_1731.required ∪ calc11_set_1732 = calc11_set_1734 := by decide +kernel

theorem calc11_set_1735_eq : calc11_card_1731.envelope ∪ calc11_set_1733 = calc11_set_1735 := by decide +kernel

theorem calc11_set_1736_eq : calc11_card_1730.required ∪ calc11_set_1734 = calc11_set_1736 := by decide +kernel

theorem calc11_set_1737_eq : calc11_card_1730.envelope ∪ calc11_set_1735 = calc11_set_1737 := by decide +kernel

theorem calc11_set_1738_eq : inline_873.envelope ∩ calc11_card_1730.envelope = calc11_set_1738 := by decide +kernel

theorem calc11_set_1739_eq : calc11_card_1731.envelope ∩ calc11_set_1738 = calc11_set_1739 := by decide +kernel

theorem calc11_set_1740_eq : calc11_set_1736 ∪ calc11_set_1739 = calc11_set_1740 := by decide +kernel

theorem calc11_finishA_1741 : calc11_set_1740.erase (5, 6) = inline_874.required := by decide +kernel

theorem calc11_finishT_1741 : insert (5, 6) calc11_set_1737 = inline_874.envelope := by decide +kernel

theorem eq_inline_874 : inline_874 = combine (5, 6) [placed 2 (5, 7) card_7, placed 3 (6, 3) card_8, inline_873] := by
  rw [calc11_card_1730_eq, calc11_card_1731_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1732_eq, calc11_set_1734_eq, calc11_set_1736_eq, calc11_set_1738_eq, calc11_set_1739_eq, calc11_set_1740_eq, calc11_finishA_1741]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1733_eq, calc11_set_1735_eq, calc11_set_1737_eq, calc11_finishT_1741]
  · decide +kernel

theorem valid_inline_874 : Valid inline_874 := by
  rw [eq_inline_874]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 7) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_8
  subst c
  exact valid_inline_873

theorem calc11_card_1742_eq : placed 4 (6, 1) card_14 = calc11_card_1742 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1743_eq : placed 2 (2, 6) card_176 = calc11_card_1743 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1744_eq : placed 0 (2, 2) card_216 = calc11_card_1744 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1745_eq : placed 1 (2, 3) card_218 = calc11_card_1745 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1746_eq : inline_874.required ∪ ∅ = calc11_set_1746 := by decide +kernel

theorem calc11_set_1747_eq : inline_874.envelope ∪ ∅ = calc11_set_1747 := by decide +kernel

theorem calc11_set_1748_eq : calc11_card_1745.required ∪ calc11_set_1746 = calc11_set_1748 := by decide +kernel

theorem calc11_set_1749_eq : calc11_card_1745.envelope ∪ calc11_set_1747 = calc11_set_1749 := by decide +kernel

theorem calc11_set_1750_eq : calc11_card_1744.required ∪ calc11_set_1748 = calc11_set_1750 := by decide +kernel

theorem calc11_set_1751_eq : calc11_card_1744.envelope ∪ calc11_set_1749 = calc11_set_1751 := by decide +kernel

theorem calc11_set_1752_eq : calc11_card_1743.required ∪ calc11_set_1750 = calc11_set_1752 := by decide +kernel

theorem calc11_set_1753_eq : calc11_card_1743.envelope ∪ calc11_set_1751 = calc11_set_1753 := by decide +kernel

theorem calc11_set_1754_eq : calc11_card_1742.required ∪ calc11_set_1752 = calc11_set_1754 := by decide +kernel

theorem calc11_set_1755_eq : calc11_card_1742.envelope ∪ calc11_set_1753 = calc11_set_1755 := by decide +kernel

theorem calc11_set_1756_eq : inline_874.envelope ∩ calc11_card_1742.envelope = calc11_set_1756 := by decide +kernel

theorem calc11_set_1757_eq : calc11_card_1745.envelope ∩ calc11_set_1756 = calc11_set_1757 := by decide +kernel

theorem calc11_set_1758_eq : calc11_card_1744.envelope ∩ calc11_set_1757 = calc11_set_1758 := by decide +kernel

theorem calc11_set_1759_eq : calc11_card_1743.envelope ∩ calc11_set_1758 = calc11_set_1759 := by decide +kernel

theorem calc11_set_1760_eq : calc11_set_1754 ∪ calc11_set_1759 = calc11_set_1760 := by decide +kernel

theorem calc11_finishA_1761 : calc11_set_1760.erase (5, 4) = card_721.required := by decide +kernel

theorem calc11_finishT_1761 : insert (5, 4) calc11_set_1755 = card_721.envelope := by decide +kernel

theorem eq_card_721 : card_721 = combine (5, 4) [placed 4 (6, 1) card_14, placed 2 (2, 6) card_176, placed 0 (2, 2) card_216, placed 1 (2, 3) card_218, inline_874] := by
  rw [calc11_card_1742_eq, calc11_card_1743_eq, calc11_card_1744_eq, calc11_card_1745_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1746_eq, calc11_set_1748_eq, calc11_set_1750_eq, calc11_set_1752_eq, calc11_set_1754_eq, calc11_set_1756_eq, calc11_set_1757_eq, calc11_set_1758_eq, calc11_set_1759_eq, calc11_set_1760_eq, calc11_finishA_1761]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1747_eq, calc11_set_1749_eq, calc11_set_1751_eq, calc11_set_1753_eq, calc11_set_1755_eq, calc11_finishT_1761]
  · decide +kernel

theorem valid_721 : Valid card_721 := by
  rw [eq_card_721]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_176
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_216
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_218
  subst c
  exact valid_inline_874

theorem calc11_card_1762_eq : placed 0 (3, 3) card_17 = calc11_card_1762 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1763_eq : placed 7 (5, 6) card_32 = calc11_card_1763 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1764_eq : calc11_card_1763.required ∪ ∅ = calc11_set_1764 := by decide +kernel

theorem calc11_set_1765_eq : calc11_card_1763.envelope ∪ ∅ = calc11_set_1765 := by decide +kernel

theorem calc11_set_1766_eq : calc11_card_1762.required ∪ calc11_set_1764 = calc11_set_1766 := by decide +kernel

theorem calc11_set_1767_eq : calc11_card_1762.envelope ∪ calc11_set_1765 = calc11_set_1767 := by decide +kernel

theorem calc11_set_1768_eq : calc11_card_1763.envelope ∩ calc11_card_1762.envelope = calc11_set_1768 := by decide +kernel

theorem calc11_set_1769_eq : calc11_set_1766 ∪ calc11_set_1768 = calc11_set_1769 := by decide +kernel

theorem calc11_finishA_1770 : calc11_set_1769.erase (3, 4) = inline_875.required := by decide +kernel

theorem calc11_finishT_1770 : insert (3, 4) calc11_set_1767 = inline_875.envelope := by decide +kernel

theorem eq_inline_875 : inline_875 = combine (3, 4) [placed 0 (3, 3) card_17, placed 7 (5, 6) card_32] := by
  rw [calc11_card_1762_eq, calc11_card_1763_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1764_eq, calc11_set_1766_eq, calc11_set_1768_eq, calc11_set_1769_eq, calc11_finishA_1770]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1765_eq, calc11_set_1767_eq, calc11_finishT_1770]
  · decide +kernel

theorem valid_inline_875 : Valid inline_875 := by
  rw [eq_inline_875]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_17
  subst c
  exact placed_valid 7 (5, 6) valid_32

theorem calc11_card_1771_eq : placed 3 (5, 3) card_8 = calc11_card_1771 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1772_eq : placed 2 (3, 7) card_9 = calc11_card_1772 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1773_eq : placed 6 (5, 8) card_366 = calc11_card_1773 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1774_eq : inline_875.required ∪ ∅ = calc11_set_1774 := by decide +kernel

theorem calc11_set_1775_eq : inline_875.envelope ∪ ∅ = calc11_set_1775 := by decide +kernel

theorem calc11_set_1776_eq : calc11_card_1773.required ∪ calc11_set_1774 = calc11_set_1776 := by decide +kernel

theorem calc11_set_1777_eq : calc11_card_1773.envelope ∪ calc11_set_1775 = calc11_set_1777 := by decide +kernel

theorem calc11_set_1778_eq : calc11_card_1772.required ∪ calc11_set_1776 = calc11_set_1778 := by decide +kernel

theorem calc11_set_1779_eq : calc11_card_1772.envelope ∪ calc11_set_1777 = calc11_set_1779 := by decide +kernel

theorem calc11_set_1780_eq : calc11_card_1771.required ∪ calc11_set_1778 = calc11_set_1780 := by decide +kernel

theorem calc11_set_1781_eq : calc11_card_1771.envelope ∪ calc11_set_1779 = calc11_set_1781 := by decide +kernel

theorem calc11_set_1782_eq : inline_875.envelope ∩ calc11_card_1771.envelope = calc11_set_1782 := by decide +kernel

theorem calc11_set_1783_eq : calc11_card_1773.envelope ∩ calc11_set_1782 = calc11_set_1783 := by decide +kernel

theorem calc11_set_1784_eq : calc11_card_1772.envelope ∩ calc11_set_1783 = calc11_set_1784 := by decide +kernel

theorem calc11_set_1785_eq : calc11_set_1780 ∪ calc11_set_1784 = calc11_set_1785 := by decide +kernel

theorem calc11_finishA_1786 : calc11_set_1785.erase (4, 6) = inline_876.required := by decide +kernel

theorem calc11_finishT_1786 : insert (4, 6) calc11_set_1781 = inline_876.envelope := by decide +kernel

theorem eq_inline_876 : inline_876 = combine (4, 6) [placed 3 (5, 3) card_8, placed 2 (3, 7) card_9, placed 6 (5, 8) card_366, inline_875] := by
  rw [calc11_card_1771_eq, calc11_card_1772_eq, calc11_card_1773_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1774_eq, calc11_set_1776_eq, calc11_set_1778_eq, calc11_set_1780_eq, calc11_set_1782_eq, calc11_set_1783_eq, calc11_set_1784_eq, calc11_set_1785_eq, calc11_finishA_1786]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1775_eq, calc11_set_1777_eq, calc11_set_1779_eq, calc11_set_1781_eq, calc11_finishT_1786]
  · decide +kernel

theorem valid_inline_876 : Valid inline_876 := by
  rw [eq_inline_876]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_366
  subst c
  exact valid_inline_875

theorem calc11_card_1787_eq : placed 6 (5, 4) card_2 = calc11_card_1787 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1788_eq : placed 1 (2, 2) card_345 = calc11_card_1788 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1789_eq : calc11_card_1788.required ∪ ∅ = calc11_set_1789 := by decide +kernel

theorem calc11_set_1790_eq : calc11_card_1788.envelope ∪ ∅ = calc11_set_1790 := by decide +kernel

theorem calc11_set_1791_eq : calc11_card_1787.required ∪ calc11_set_1789 = calc11_set_1791 := by decide +kernel

theorem calc11_set_1792_eq : calc11_card_1787.envelope ∪ calc11_set_1790 = calc11_set_1792 := by decide +kernel

theorem calc11_set_1793_eq : calc11_card_1788.envelope ∩ calc11_card_1787.envelope = calc11_set_1793 := by decide +kernel

theorem calc11_set_1794_eq : calc11_set_1791 ∪ calc11_set_1793 = calc11_set_1794 := by decide +kernel

theorem calc11_finishA_1795 : calc11_set_1794.erase (5, 4) = inline_877.required := by decide +kernel

theorem calc11_finishT_1795 : insert (5, 4) calc11_set_1792 = inline_877.envelope := by decide +kernel

theorem eq_inline_877 : inline_877 = combine (5, 4) [placed 6 (5, 4) card_2, placed 1 (2, 2) card_345] := by
  rw [calc11_card_1787_eq, calc11_card_1788_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1789_eq, calc11_set_1791_eq, calc11_set_1793_eq, calc11_set_1794_eq, calc11_finishA_1795]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1790_eq, calc11_set_1792_eq, calc11_finishT_1795]
  · decide +kernel

theorem valid_inline_877 : Valid inline_877 := by
  rw [eq_inline_877]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_2
  subst c
  exact placed_valid 1 (2, 2) valid_345

theorem calc11_card_1796_eq : placed 6 (5, 4) card_0 = calc11_card_1796 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1797_eq : placed 4 (5, 2) card_307 = calc11_card_1797 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1798_eq : calc11_card_1797.required ∪ ∅ = calc11_set_1798 := by decide +kernel

theorem calc11_set_1799_eq : calc11_card_1797.envelope ∪ ∅ = calc11_set_1799 := by decide +kernel

theorem calc11_set_1800_eq : calc11_card_1796.required ∪ calc11_set_1798 = calc11_set_1800 := by decide +kernel

theorem calc11_set_1801_eq : calc11_card_1796.envelope ∪ calc11_set_1799 = calc11_set_1801 := by decide +kernel

theorem calc11_set_1802_eq : calc11_card_1797.envelope ∩ calc11_card_1796.envelope = calc11_set_1802 := by decide +kernel

theorem calc11_set_1803_eq : calc11_set_1800 ∪ calc11_set_1802 = calc11_set_1803 := by decide +kernel

theorem calc11_finishA_1804 : calc11_set_1803.erase (3, 4) = inline_878.required := by decide +kernel

theorem calc11_finishT_1804 : insert (3, 4) calc11_set_1801 = inline_878.envelope := by decide +kernel

theorem eq_inline_878 : inline_878 = combine (3, 4) [placed 6 (5, 4) card_0, placed 4 (5, 2) card_307] := by
  rw [calc11_card_1796_eq, calc11_card_1797_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1798_eq, calc11_set_1800_eq, calc11_set_1802_eq, calc11_set_1803_eq, calc11_finishA_1804]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1799_eq, calc11_set_1801_eq, calc11_finishT_1804]
  · decide +kernel

theorem valid_inline_878 : Valid inline_878 := by
  rw [eq_inline_878]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_0
  subst c
  exact placed_valid 4 (5, 2) valid_307

theorem calc11_card_1805_eq : placed 6 (5, 4) card_0 = calc11_card_1805 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1806_eq : placed 0 (2, 1) card_267 = calc11_card_1806 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1807_eq : calc11_card_1806.required ∪ ∅ = calc11_set_1807 := by decide +kernel

theorem calc11_set_1808_eq : calc11_card_1806.envelope ∪ ∅ = calc11_set_1808 := by decide +kernel

theorem calc11_set_1809_eq : calc11_card_1805.required ∪ calc11_set_1807 = calc11_set_1809 := by decide +kernel

theorem calc11_set_1810_eq : calc11_card_1805.envelope ∪ calc11_set_1808 = calc11_set_1810 := by decide +kernel

theorem calc11_set_1811_eq : calc11_card_1806.envelope ∩ calc11_card_1805.envelope = calc11_set_1811 := by decide +kernel

theorem calc11_set_1812_eq : calc11_set_1809 ∪ calc11_set_1811 = calc11_set_1812 := by decide +kernel

theorem calc11_finishA_1813 : calc11_set_1812.erase (3, 4) = inline_879.required := by decide +kernel

theorem calc11_finishT_1813 : insert (3, 4) calc11_set_1810 = inline_879.envelope := by decide +kernel

theorem eq_inline_879 : inline_879 = combine (3, 4) [placed 6 (5, 4) card_0, placed 0 (2, 1) card_267] := by
  rw [calc11_card_1805_eq, calc11_card_1806_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1807_eq, calc11_set_1809_eq, calc11_set_1811_eq, calc11_set_1812_eq, calc11_finishA_1813]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1808_eq, calc11_set_1810_eq, calc11_finishT_1813]
  · decide +kernel

theorem valid_inline_879 : Valid inline_879 := by
  rw [eq_inline_879]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_0
  subst c
  exact placed_valid 0 (2, 1) valid_267

theorem calc11_card_1814_eq : placed 4 (5, 1) card_13 = calc11_card_1814 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1815_eq : placed 2 (1, 6) card_176 = calc11_card_1815 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1816_eq : inline_879.required ∪ ∅ = calc11_set_1816 := by decide +kernel

theorem calc11_set_1817_eq : inline_879.envelope ∪ ∅ = calc11_set_1817 := by decide +kernel

theorem calc11_set_1818_eq : inline_878.required ∪ calc11_set_1816 = calc11_set_1818 := by decide +kernel

theorem calc11_set_1819_eq : inline_878.envelope ∪ calc11_set_1817 = calc11_set_1819 := by decide +kernel

theorem calc11_set_1820_eq : inline_877.required ∪ calc11_set_1818 = calc11_set_1820 := by decide +kernel

theorem calc11_set_1821_eq : inline_877.envelope ∪ calc11_set_1819 = calc11_set_1821 := by decide +kernel

theorem calc11_set_1822_eq : inline_876.required ∪ calc11_set_1820 = calc11_set_1822 := by decide +kernel

theorem calc11_set_1823_eq : inline_876.envelope ∪ calc11_set_1821 = calc11_set_1823 := by decide +kernel

theorem calc11_set_1824_eq : calc11_card_1815.required ∪ calc11_set_1822 = calc11_set_1824 := by decide +kernel

theorem calc11_set_1825_eq : calc11_card_1815.envelope ∪ calc11_set_1823 = calc11_set_1825 := by decide +kernel

theorem calc11_set_1826_eq : calc11_card_1814.required ∪ calc11_set_1824 = calc11_set_1826 := by decide +kernel

theorem calc11_set_1827_eq : calc11_card_1814.envelope ∪ calc11_set_1825 = calc11_set_1827 := by decide +kernel

theorem calc11_set_1828_eq : inline_879.envelope ∩ calc11_card_1814.envelope = calc11_set_1828 := by decide +kernel

theorem calc11_set_1829_eq : inline_878.envelope ∩ calc11_set_1828 = calc11_set_1829 := by decide +kernel

theorem calc11_set_1830_eq : inline_877.envelope ∩ calc11_set_1829 = calc11_set_1830 := by decide +kernel

theorem calc11_set_1831_eq : inline_876.envelope ∩ calc11_set_1830 = calc11_set_1831 := by decide +kernel

theorem calc11_set_1832_eq : calc11_card_1815.envelope ∩ calc11_set_1831 = calc11_set_1832 := by decide +kernel

theorem calc11_set_1833_eq : calc11_set_1826 ∪ calc11_set_1832 = calc11_set_1833 := by decide +kernel

theorem calc11_finishA_1834 : calc11_set_1833.erase (4, 4) = card_722.required := by decide +kernel

theorem calc11_finishT_1834 : insert (4, 4) calc11_set_1827 = card_722.envelope := by decide +kernel

theorem eq_card_722 : card_722 = combine (4, 4) [placed 4 (5, 1) card_13, placed 2 (1, 6) card_176, inline_876, inline_877, inline_878, inline_879] := by
  rw [calc11_card_1814_eq, calc11_card_1815_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1816_eq, calc11_set_1818_eq, calc11_set_1820_eq, calc11_set_1822_eq, calc11_set_1824_eq, calc11_set_1826_eq, calc11_set_1828_eq, calc11_set_1829_eq, calc11_set_1830_eq, calc11_set_1831_eq, calc11_set_1832_eq, calc11_set_1833_eq, calc11_finishA_1834]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1817_eq, calc11_set_1819_eq, calc11_set_1821_eq, calc11_set_1823_eq, calc11_set_1825_eq, calc11_set_1827_eq, calc11_finishT_1834]
  · decide +kernel

theorem valid_722 : Valid card_722 := by
  rw [eq_card_722]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_176
  rcases hc with rfl | hc
  · exact valid_inline_876
  rcases hc with rfl | hc
  · exact valid_inline_877
  rcases hc with rfl | hc
  · exact valid_inline_878
  subst c
  exact valid_inline_879

theorem calc11_card_1835_eq : placed 6 (5, 7) card_46 = calc11_card_1835 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1836_eq : placed 0 (2, 1) card_321 = calc11_card_1836 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1837_eq : calc11_card_1836.required ∪ ∅ = calc11_set_1837 := by decide +kernel

theorem calc11_set_1838_eq : calc11_card_1836.envelope ∪ ∅ = calc11_set_1838 := by decide +kernel

theorem calc11_set_1839_eq : calc11_card_1835.required ∪ calc11_set_1837 = calc11_set_1839 := by decide +kernel

theorem calc11_set_1840_eq : calc11_card_1835.envelope ∪ calc11_set_1838 = calc11_set_1840 := by decide +kernel

theorem calc11_set_1841_eq : calc11_card_1836.envelope ∩ calc11_card_1835.envelope = calc11_set_1841 := by decide +kernel

theorem calc11_set_1842_eq : calc11_set_1839 ∪ calc11_set_1841 = calc11_set_1842 := by decide +kernel

theorem calc11_finishA_1843 : calc11_set_1842.erase (4, 5) = inline_880.required := by decide +kernel

theorem calc11_finishT_1843 : insert (4, 5) calc11_set_1840 = inline_880.envelope := by decide +kernel

theorem eq_inline_880 : inline_880 = combine (4, 5) [placed 6 (5, 7) card_46, placed 0 (2, 1) card_321] := by
  rw [calc11_card_1835_eq, calc11_card_1836_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1837_eq, calc11_set_1839_eq, calc11_set_1841_eq, calc11_set_1842_eq, calc11_finishA_1843]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1838_eq, calc11_set_1840_eq, calc11_finishT_1843]
  · decide +kernel

theorem valid_inline_880 : Valid inline_880 := by
  rw [eq_inline_880]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_46
  subst c
  exact placed_valid 0 (2, 1) valid_321

theorem calc11_card_1844_eq : placed 6 (3, 8) card_53 = calc11_card_1844 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1845_eq : placed 0 (2, 2) card_53 = calc11_card_1845 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1846_eq : placed 1 (1, 4) card_310 = calc11_card_1846 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1847_eq : calc11_card_1846.required ∪ ∅ = calc11_set_1847 := by decide +kernel

theorem calc11_set_1848_eq : calc11_card_1846.envelope ∪ ∅ = calc11_set_1848 := by decide +kernel

theorem calc11_set_1849_eq : calc11_card_1845.required ∪ calc11_set_1847 = calc11_set_1849 := by decide +kernel

theorem calc11_set_1850_eq : calc11_card_1845.envelope ∪ calc11_set_1848 = calc11_set_1850 := by decide +kernel

theorem calc11_set_1851_eq : calc11_card_1844.required ∪ calc11_set_1849 = calc11_set_1851 := by decide +kernel

theorem calc11_set_1852_eq : calc11_card_1844.envelope ∪ calc11_set_1850 = calc11_set_1852 := by decide +kernel

theorem calc11_set_1853_eq : calc11_card_1846.envelope ∩ calc11_card_1844.envelope = calc11_set_1853 := by decide +kernel

theorem calc11_set_1854_eq : calc11_card_1845.envelope ∩ calc11_set_1853 = calc11_set_1854 := by decide +kernel

theorem calc11_set_1855_eq : calc11_set_1851 ∪ calc11_set_1854 = calc11_set_1855 := by decide +kernel

theorem calc11_finishA_1856 : calc11_set_1855.erase (2, 4) = inline_881.required := by decide +kernel

theorem calc11_finishT_1856 : insert (2, 4) calc11_set_1852 = inline_881.envelope := by decide +kernel

theorem eq_inline_881 : inline_881 = combine (2, 4) [placed 6 (3, 8) card_53, placed 0 (2, 2) card_53, placed 1 (1, 4) card_310] := by
  rw [calc11_card_1844_eq, calc11_card_1845_eq, calc11_card_1846_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1847_eq, calc11_set_1849_eq, calc11_set_1851_eq, calc11_set_1853_eq, calc11_set_1854_eq, calc11_set_1855_eq, calc11_finishA_1856]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1848_eq, calc11_set_1850_eq, calc11_set_1852_eq, calc11_finishT_1856]
  · decide +kernel

theorem valid_inline_881 : Valid inline_881 := by
  rw [eq_inline_881]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 8) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_53
  subst c
  exact placed_valid 1 (1, 4) valid_310

theorem calc11_card_1857_eq : placed 6 (4, 8) card_9 = calc11_card_1857 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1858_eq : placed 5 (2, 7) card_90 = calc11_card_1858 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1859_eq : placed 3 (6, 4) card_99 = calc11_card_1859 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1860_eq : calc11_card_1859.required ∪ ∅ = calc11_set_1860 := by decide +kernel

theorem calc11_set_1861_eq : calc11_card_1859.envelope ∪ ∅ = calc11_set_1861 := by decide +kernel

theorem calc11_set_1862_eq : calc11_card_1858.required ∪ calc11_set_1860 = calc11_set_1862 := by decide +kernel

theorem calc11_set_1863_eq : calc11_card_1858.envelope ∪ calc11_set_1861 = calc11_set_1863 := by decide +kernel

theorem calc11_set_1864_eq : calc11_card_1857.required ∪ calc11_set_1862 = calc11_set_1864 := by decide +kernel

theorem calc11_set_1865_eq : calc11_card_1857.envelope ∪ calc11_set_1863 = calc11_set_1865 := by decide +kernel

theorem calc11_set_1866_eq : calc11_card_1859.envelope ∩ calc11_card_1857.envelope = calc11_set_1866 := by decide +kernel

theorem calc11_set_1867_eq : calc11_card_1858.envelope ∩ calc11_set_1866 = calc11_set_1867 := by decide +kernel

theorem calc11_set_1868_eq : calc11_set_1864 ∪ calc11_set_1867 = calc11_set_1868 := by decide +kernel

theorem calc11_finishA_1869 : calc11_set_1868.erase (3, 4) = inline_882.required := by decide +kernel

theorem calc11_finishT_1869 : insert (3, 4) calc11_set_1865 = inline_882.envelope := by decide +kernel

theorem eq_inline_882 : inline_882 = combine (3, 4) [placed 6 (4, 8) card_9, placed 5 (2, 7) card_90, placed 3 (6, 4) card_99] := by
  rw [calc11_card_1857_eq, calc11_card_1858_eq, calc11_card_1859_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1860_eq, calc11_set_1862_eq, calc11_set_1864_eq, calc11_set_1866_eq, calc11_set_1867_eq, calc11_set_1868_eq, calc11_finishA_1869]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1861_eq, calc11_set_1863_eq, calc11_set_1865_eq, calc11_finishT_1869]
  · decide +kernel

theorem valid_inline_882 : Valid inline_882 := by
  rw [eq_inline_882]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 8) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_90
  subst c
  exact placed_valid 3 (6, 4) valid_99

theorem calc11_card_1870_eq : placed 6 (3, 8) card_44 = calc11_card_1870 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1871_eq : placed 6 (3, 8) card_52 = calc11_card_1871 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1872_eq : placed 3 (5, 4) card_180 = calc11_card_1872 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1873_eq : inline_882.required ∪ ∅ = calc11_set_1873 := by decide +kernel

theorem calc11_set_1874_eq : inline_882.envelope ∪ ∅ = calc11_set_1874 := by decide +kernel

theorem calc11_set_1875_eq : calc11_card_1872.required ∪ calc11_set_1873 = calc11_set_1875 := by decide +kernel

theorem calc11_set_1876_eq : calc11_card_1872.envelope ∪ calc11_set_1874 = calc11_set_1876 := by decide +kernel

theorem calc11_set_1877_eq : calc11_card_1871.required ∪ calc11_set_1875 = calc11_set_1877 := by decide +kernel

theorem calc11_set_1878_eq : calc11_card_1871.envelope ∪ calc11_set_1876 = calc11_set_1878 := by decide +kernel

theorem calc11_set_1879_eq : calc11_card_1870.required ∪ calc11_set_1877 = calc11_set_1879 := by decide +kernel

theorem calc11_set_1880_eq : calc11_card_1870.envelope ∪ calc11_set_1878 = calc11_set_1880 := by decide +kernel

theorem calc11_set_1881_eq : inline_882.envelope ∩ calc11_card_1870.envelope = calc11_set_1881 := by decide +kernel

theorem calc11_set_1882_eq : calc11_card_1872.envelope ∩ calc11_set_1881 = calc11_set_1882 := by decide +kernel

theorem calc11_set_1883_eq : calc11_card_1871.envelope ∩ calc11_set_1882 = calc11_set_1883 := by decide +kernel

theorem calc11_set_1884_eq : calc11_set_1879 ∪ calc11_set_1883 = calc11_set_1884 := by decide +kernel

theorem calc11_finishA_1885 : calc11_set_1884.erase (3, 7) = inline_883.required := by decide +kernel

theorem calc11_finishT_1885 : insert (3, 7) calc11_set_1880 = inline_883.envelope := by decide +kernel

theorem eq_inline_883 : inline_883 = combine (3, 7) [placed 6 (3, 8) card_44, placed 6 (3, 8) card_52, placed 3 (5, 4) card_180, inline_882] := by
  rw [calc11_card_1870_eq, calc11_card_1871_eq, calc11_card_1872_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1873_eq, calc11_set_1875_eq, calc11_set_1877_eq, calc11_set_1879_eq, calc11_set_1881_eq, calc11_set_1882_eq, calc11_set_1883_eq, calc11_set_1884_eq, calc11_finishA_1885]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1874_eq, calc11_set_1876_eq, calc11_set_1878_eq, calc11_set_1880_eq, calc11_finishT_1885]
  · decide +kernel

theorem valid_inline_883 : Valid inline_883 := by
  rw [eq_inline_883]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 8) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 8) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 4) valid_180
  subst c
  exact valid_inline_882

theorem calc11_card_1886_eq : placed 0 (2, 4) card_82 = calc11_card_1886 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1887_eq : placed 2 (2, 8) card_176 = calc11_card_1887 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1888_eq : placed 1 (2, 5) card_218 = calc11_card_1888 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1889_eq : placed 6 (6, 10) card_369 = calc11_card_1889 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1890_eq : calc11_card_1889.required ∪ ∅ = calc11_set_1890 := by decide +kernel

theorem calc11_set_1891_eq : calc11_card_1889.envelope ∪ ∅ = calc11_set_1891 := by decide +kernel

theorem calc11_set_1892_eq : calc11_card_1888.required ∪ calc11_set_1890 = calc11_set_1892 := by decide +kernel

theorem calc11_set_1893_eq : calc11_card_1888.envelope ∪ calc11_set_1891 = calc11_set_1893 := by decide +kernel

theorem calc11_set_1894_eq : calc11_card_1887.required ∪ calc11_set_1892 = calc11_set_1894 := by decide +kernel

theorem calc11_set_1895_eq : calc11_card_1887.envelope ∪ calc11_set_1893 = calc11_set_1895 := by decide +kernel

theorem calc11_set_1896_eq : calc11_card_1886.required ∪ calc11_set_1894 = calc11_set_1896 := by decide +kernel

theorem calc11_set_1897_eq : calc11_card_1886.envelope ∪ calc11_set_1895 = calc11_set_1897 := by decide +kernel

theorem calc11_set_1898_eq : calc11_card_1889.envelope ∩ calc11_card_1886.envelope = calc11_set_1898 := by decide +kernel

theorem calc11_set_1899_eq : calc11_card_1888.envelope ∩ calc11_set_1898 = calc11_set_1899 := by decide +kernel

theorem calc11_set_1900_eq : calc11_card_1887.envelope ∩ calc11_set_1899 = calc11_set_1900 := by decide +kernel

theorem calc11_set_1901_eq : calc11_set_1896 ∪ calc11_set_1900 = calc11_set_1901 := by decide +kernel

theorem calc11_finishA_1902 : calc11_set_1901.erase (5, 6) = inline_884.required := by decide +kernel

theorem calc11_finishT_1902 : insert (5, 6) calc11_set_1897 = inline_884.envelope := by decide +kernel

theorem eq_inline_884 : inline_884 = combine (5, 6) [placed 0 (2, 4) card_82, placed 2 (2, 8) card_176, placed 1 (2, 5) card_218, placed 6 (6, 10) card_369] := by
  rw [calc11_card_1886_eq, calc11_card_1887_eq, calc11_card_1888_eq, calc11_card_1889_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1890_eq, calc11_set_1892_eq, calc11_set_1894_eq, calc11_set_1896_eq, calc11_set_1898_eq, calc11_set_1899_eq, calc11_set_1900_eq, calc11_set_1901_eq, calc11_finishA_1902]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1891_eq, calc11_set_1893_eq, calc11_set_1895_eq, calc11_set_1897_eq, calc11_finishT_1902]
  · decide +kernel

theorem valid_inline_884 : Valid inline_884 := by
  rw [eq_inline_884]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_82
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_176
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_218
  subst c
  exact placed_valid 6 (6, 10) valid_369

theorem calc11_card_1903_eq : placed 1 (2, 4) card_145 = calc11_card_1903 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1904_eq : placed 5 (2, 7) card_314 = calc11_card_1904 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1905_eq : calc11_card_1904.required ∪ ∅ = calc11_set_1905 := by decide +kernel

theorem calc11_set_1906_eq : calc11_card_1904.envelope ∪ ∅ = calc11_set_1906 := by decide +kernel

theorem calc11_set_1907_eq : calc11_card_1903.required ∪ calc11_set_1905 = calc11_set_1907 := by decide +kernel

theorem calc11_set_1908_eq : calc11_card_1903.envelope ∪ calc11_set_1906 = calc11_set_1908 := by decide +kernel

theorem calc11_set_1909_eq : calc11_card_1904.envelope ∩ calc11_card_1903.envelope = calc11_set_1909 := by decide +kernel

theorem calc11_set_1910_eq : calc11_set_1907 ∪ calc11_set_1909 = calc11_set_1910 := by decide +kernel

theorem calc11_finishA_1911 : calc11_set_1910.erase (3, 4) = inline_885.required := by decide +kernel

theorem calc11_finishT_1911 : insert (3, 4) calc11_set_1908 = inline_885.envelope := by decide +kernel

theorem eq_inline_885 : inline_885 = combine (3, 4) [placed 1 (2, 4) card_145, placed 5 (2, 7) card_314] := by
  rw [calc11_card_1903_eq, calc11_card_1904_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1905_eq, calc11_set_1907_eq, calc11_set_1909_eq, calc11_set_1910_eq, calc11_finishA_1911]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1906_eq, calc11_set_1908_eq, calc11_finishT_1911]
  · decide +kernel

theorem valid_inline_885 : Valid inline_885 := by
  rw [eq_inline_885]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_145
  subst c
  exact placed_valid 5 (2, 7) valid_314

theorem calc11_card_1912_eq : placed 6 (3, 8) card_44 = calc11_card_1912 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1913_eq : placed 6 (3, 8) card_52 = calc11_card_1913 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1914_eq : placed 3 (5, 4) card_180 = calc11_card_1914 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1915_eq : inline_885.required ∪ ∅ = calc11_set_1915 := by decide +kernel

theorem calc11_set_1916_eq : inline_885.envelope ∪ ∅ = calc11_set_1916 := by decide +kernel

theorem calc11_set_1917_eq : calc11_card_1914.required ∪ calc11_set_1915 = calc11_set_1917 := by decide +kernel

theorem calc11_set_1918_eq : calc11_card_1914.envelope ∪ calc11_set_1916 = calc11_set_1918 := by decide +kernel

theorem calc11_set_1919_eq : calc11_card_1913.required ∪ calc11_set_1917 = calc11_set_1919 := by decide +kernel

theorem calc11_set_1920_eq : calc11_card_1913.envelope ∪ calc11_set_1918 = calc11_set_1920 := by decide +kernel

theorem calc11_set_1921_eq : calc11_card_1912.required ∪ calc11_set_1919 = calc11_set_1921 := by decide +kernel

theorem calc11_set_1922_eq : calc11_card_1912.envelope ∪ calc11_set_1920 = calc11_set_1922 := by decide +kernel

theorem calc11_set_1923_eq : inline_885.envelope ∩ calc11_card_1912.envelope = calc11_set_1923 := by decide +kernel

theorem calc11_set_1924_eq : calc11_card_1914.envelope ∩ calc11_set_1923 = calc11_set_1924 := by decide +kernel

theorem calc11_set_1925_eq : calc11_card_1913.envelope ∩ calc11_set_1924 = calc11_set_1925 := by decide +kernel

theorem calc11_set_1926_eq : calc11_set_1921 ∪ calc11_set_1925 = calc11_set_1926 := by decide +kernel

theorem calc11_finishA_1927 : calc11_set_1926.erase (3, 7) = inline_886.required := by decide +kernel

theorem calc11_finishT_1927 : insert (3, 7) calc11_set_1922 = inline_886.envelope := by decide +kernel

theorem eq_inline_886 : inline_886 = combine (3, 7) [placed 6 (3, 8) card_44, placed 6 (3, 8) card_52, placed 3 (5, 4) card_180, inline_885] := by
  rw [calc11_card_1912_eq, calc11_card_1913_eq, calc11_card_1914_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1915_eq, calc11_set_1917_eq, calc11_set_1919_eq, calc11_set_1921_eq, calc11_set_1923_eq, calc11_set_1924_eq, calc11_set_1925_eq, calc11_set_1926_eq, calc11_finishA_1927]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1916_eq, calc11_set_1918_eq, calc11_set_1920_eq, calc11_set_1922_eq, calc11_finishT_1927]
  · decide +kernel

theorem valid_inline_886 : Valid inline_886 := by
  rw [eq_inline_886]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 8) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 8) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 4) valid_180
  subst c
  exact valid_inline_885

theorem calc11_card_1928_eq : placed 4 (6, 3) card_13 = calc11_card_1928 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1929_eq : placed 2 (4, 9) card_192 = calc11_card_1929 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1930_eq : placed 6 (6, 10) card_369 = calc11_card_1930 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1931_eq : placed 1 (2, 4) card_435 = calc11_card_1931 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1932_eq : placed 1 (3, 4) card_474 = calc11_card_1932 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1933_eq : placed 5 (3, 8) card_477 = calc11_card_1933 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1934_eq : calc11_card_1933.required ∪ ∅ = calc11_set_1934 := by decide +kernel

theorem calc11_set_1935_eq : calc11_card_1933.envelope ∪ ∅ = calc11_set_1935 := by decide +kernel

theorem calc11_set_1936_eq : calc11_card_1932.required ∪ calc11_set_1934 = calc11_set_1936 := by decide +kernel

theorem calc11_set_1937_eq : calc11_card_1932.envelope ∪ calc11_set_1935 = calc11_set_1937 := by decide +kernel

theorem calc11_set_1938_eq : calc11_card_1931.required ∪ calc11_set_1936 = calc11_set_1938 := by decide +kernel

theorem calc11_set_1939_eq : calc11_card_1931.envelope ∪ calc11_set_1937 = calc11_set_1939 := by decide +kernel

theorem calc11_set_1940_eq : calc11_card_1930.required ∪ calc11_set_1938 = calc11_set_1940 := by decide +kernel

theorem calc11_set_1941_eq : calc11_card_1930.envelope ∪ calc11_set_1939 = calc11_set_1941 := by decide +kernel

theorem calc11_set_1942_eq : calc11_card_1929.required ∪ calc11_set_1940 = calc11_set_1942 := by decide +kernel

theorem calc11_set_1943_eq : calc11_card_1929.envelope ∪ calc11_set_1941 = calc11_set_1943 := by decide +kernel

theorem calc11_set_1944_eq : calc11_card_1928.required ∪ calc11_set_1942 = calc11_set_1944 := by decide +kernel

theorem calc11_set_1945_eq : calc11_card_1928.envelope ∪ calc11_set_1943 = calc11_set_1945 := by decide +kernel

theorem calc11_set_1946_eq : calc11_card_1933.envelope ∩ calc11_card_1928.envelope = calc11_set_1946 := by decide +kernel

theorem calc11_set_1947_eq : calc11_card_1932.envelope ∩ calc11_set_1946 = calc11_set_1947 := by decide +kernel

theorem calc11_set_1948_eq : calc11_card_1931.envelope ∩ calc11_set_1947 = calc11_set_1948 := by decide +kernel

theorem calc11_set_1949_eq : calc11_card_1930.envelope ∩ calc11_set_1948 = calc11_set_1949 := by decide +kernel

theorem calc11_set_1950_eq : calc11_card_1929.envelope ∩ calc11_set_1949 = calc11_set_1950 := by decide +kernel

theorem calc11_set_1951_eq : calc11_set_1944 ∪ calc11_set_1950 = calc11_set_1951 := by decide +kernel

theorem calc11_finishA_1952 : calc11_set_1951.erase (5, 6) = inline_887.required := by decide +kernel

theorem calc11_finishT_1952 : insert (5, 6) calc11_set_1945 = inline_887.envelope := by decide +kernel

theorem eq_inline_887 : inline_887 = combine (5, 6) [placed 4 (6, 3) card_13, placed 2 (4, 9) card_192, placed 6 (6, 10) card_369, placed 1 (2, 4) card_435, placed 1 (3, 4) card_474, placed 5 (3, 8) card_477] := by
  rw [calc11_card_1928_eq, calc11_card_1929_eq, calc11_card_1930_eq, calc11_card_1931_eq, calc11_card_1932_eq, calc11_card_1933_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1934_eq, calc11_set_1936_eq, calc11_set_1938_eq, calc11_set_1940_eq, calc11_set_1942_eq, calc11_set_1944_eq, calc11_set_1946_eq, calc11_set_1947_eq, calc11_set_1948_eq, calc11_set_1949_eq, calc11_set_1950_eq, calc11_set_1951_eq, calc11_finishA_1952]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1935_eq, calc11_set_1937_eq, calc11_set_1939_eq, calc11_set_1941_eq, calc11_set_1943_eq, calc11_set_1945_eq, calc11_finishT_1952]
  · decide +kernel

theorem valid_inline_887 : Valid inline_887 := by
  rw [eq_inline_887]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 9) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 10) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_474
  subst c
  exact placed_valid 5 (3, 8) valid_477

theorem calc11_card_1953_eq : placed 0 (0, 2) card_721 = calc11_card_1953 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1954_eq : placed 0 (1, 2) card_722 = calc11_card_1954 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1955_eq : calc11_card_1954.required ∪ ∅ = calc11_set_1955 := by decide +kernel

theorem calc11_set_1956_eq : calc11_card_1954.envelope ∪ ∅ = calc11_set_1956 := by decide +kernel

theorem calc11_set_1957_eq : calc11_card_1953.required ∪ calc11_set_1955 = calc11_set_1957 := by decide +kernel

theorem calc11_set_1958_eq : calc11_card_1953.envelope ∪ calc11_set_1956 = calc11_set_1958 := by decide +kernel

theorem calc11_set_1959_eq : inline_887.required ∪ calc11_set_1957 = calc11_set_1959 := by decide +kernel

theorem calc11_set_1960_eq : inline_887.envelope ∪ calc11_set_1958 = calc11_set_1960 := by decide +kernel

theorem calc11_set_1961_eq : inline_886.required ∪ calc11_set_1959 = calc11_set_1961 := by decide +kernel

theorem calc11_set_1962_eq : inline_886.envelope ∪ calc11_set_1960 = calc11_set_1962 := by decide +kernel

theorem calc11_set_1963_eq : inline_884.required ∪ calc11_set_1961 = calc11_set_1963 := by decide +kernel

theorem calc11_set_1964_eq : inline_884.envelope ∪ calc11_set_1962 = calc11_set_1964 := by decide +kernel

theorem calc11_set_1965_eq : inline_883.required ∪ calc11_set_1963 = calc11_set_1965 := by decide +kernel

theorem calc11_set_1966_eq : inline_883.envelope ∪ calc11_set_1964 = calc11_set_1966 := by decide +kernel

theorem calc11_set_1967_eq : calc11_card_1954.envelope ∩ inline_883.envelope = calc11_set_1967 := by decide +kernel

theorem calc11_set_1968_eq : calc11_card_1953.envelope ∩ calc11_set_1967 = calc11_set_1968 := by decide +kernel

theorem calc11_set_1969_eq : inline_887.envelope ∩ calc11_set_1968 = calc11_set_1969 := by decide +kernel

theorem calc11_set_1970_eq : inline_886.envelope ∩ calc11_set_1969 = calc11_set_1970 := by decide +kernel

theorem calc11_set_1971_eq : inline_884.envelope ∩ calc11_set_1970 = calc11_set_1971 := by decide +kernel

theorem calc11_set_1972_eq : calc11_set_1965 ∪ calc11_set_1971 = calc11_set_1972 := by decide +kernel

theorem calc11_finishA_1973 : calc11_set_1972.erase (5, 7) = inline_888.required := by decide +kernel

theorem calc11_finishT_1973 : insert (5, 7) calc11_set_1966 = inline_888.envelope := by decide +kernel

theorem eq_inline_888 : inline_888 = combine (5, 7) [inline_883, inline_884, inline_886, inline_887, placed 0 (0, 2) card_721, placed 0 (1, 2) card_722] := by
  rw [calc11_card_1953_eq, calc11_card_1954_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1955_eq, calc11_set_1957_eq, calc11_set_1959_eq, calc11_set_1961_eq, calc11_set_1963_eq, calc11_set_1965_eq, calc11_set_1967_eq, calc11_set_1968_eq, calc11_set_1969_eq, calc11_set_1970_eq, calc11_set_1971_eq, calc11_set_1972_eq, calc11_finishA_1973]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1956_eq, calc11_set_1958_eq, calc11_set_1960_eq, calc11_set_1962_eq, calc11_set_1964_eq, calc11_set_1966_eq, calc11_finishT_1973]
  · decide +kernel

theorem valid_inline_888 : Valid inline_888 := by
  rw [eq_inline_888]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_883
  rcases hc with rfl | hc
  · exact valid_inline_884
  rcases hc with rfl | hc
  · exact valid_inline_886
  rcases hc with rfl | hc
  · exact valid_inline_887
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_721
  subst c
  exact placed_valid 0 (1, 2) valid_722

theorem calc11_card_1974_eq : placed 0 (1, 1) card_328 = calc11_card_1974 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1975_eq : placed 0 (1, 1) card_330 = calc11_card_1975 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1976_eq : inline_888.required ∪ ∅ = calc11_set_1976 := by decide +kernel

theorem calc11_set_1977_eq : inline_888.envelope ∪ ∅ = calc11_set_1977 := by decide +kernel

theorem calc11_set_1978_eq : inline_881.required ∪ calc11_set_1976 = calc11_set_1978 := by decide +kernel

theorem calc11_set_1979_eq : inline_881.envelope ∪ calc11_set_1977 = calc11_set_1979 := by decide +kernel

theorem calc11_set_1980_eq : inline_880.required ∪ calc11_set_1978 = calc11_set_1980 := by decide +kernel

theorem calc11_set_1981_eq : inline_880.envelope ∪ calc11_set_1979 = calc11_set_1981 := by decide +kernel

theorem calc11_set_1982_eq : calc11_card_1975.required ∪ calc11_set_1980 = calc11_set_1982 := by decide +kernel

theorem calc11_set_1983_eq : calc11_card_1975.envelope ∪ calc11_set_1981 = calc11_set_1983 := by decide +kernel

theorem calc11_set_1984_eq : calc11_card_1974.required ∪ calc11_set_1982 = calc11_set_1984 := by decide +kernel

theorem calc11_set_1985_eq : calc11_card_1974.envelope ∪ calc11_set_1983 = calc11_set_1985 := by decide +kernel

theorem calc11_set_1986_eq : inline_888.envelope ∩ calc11_card_1974.envelope = calc11_set_1986 := by decide +kernel

theorem calc11_set_1987_eq : inline_881.envelope ∩ calc11_set_1986 = calc11_set_1987 := by decide +kernel

theorem calc11_set_1988_eq : inline_880.envelope ∩ calc11_set_1987 = calc11_set_1988 := by decide +kernel

theorem calc11_set_1989_eq : calc11_card_1975.envelope ∩ calc11_set_1988 = calc11_set_1989 := by decide +kernel

theorem calc11_set_1990_eq : calc11_set_1984 ∪ calc11_set_1989 = calc11_set_1990 := by decide +kernel

theorem calc11_finishA_1991 : calc11_set_1990.erase (5, 5) = card_723.required := by decide +kernel

theorem calc11_finishT_1991 : insert (5, 5) calc11_set_1985 = card_723.envelope := by decide +kernel

theorem eq_card_723 : card_723 = combine (5, 5) [placed 0 (1, 1) card_328, placed 0 (1, 1) card_330, inline_880, inline_881, inline_888] := by
  rw [calc11_card_1974_eq, calc11_card_1975_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1976_eq, calc11_set_1978_eq, calc11_set_1980_eq, calc11_set_1982_eq, calc11_set_1984_eq, calc11_set_1986_eq, calc11_set_1987_eq, calc11_set_1988_eq, calc11_set_1989_eq, calc11_set_1990_eq, calc11_finishA_1991]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1977_eq, calc11_set_1979_eq, calc11_set_1981_eq, calc11_set_1983_eq, calc11_set_1985_eq, calc11_finishT_1991]
  · decide +kernel

theorem valid_723 : Valid card_723 := by
  rw [eq_card_723]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_328
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_330
  rcases hc with rfl | hc
  · exact valid_inline_880
  rcases hc with rfl | hc
  · exact valid_inline_881
  subst c
  exact valid_inline_888

theorem calc11_card_1992_eq : placed 0 (3, 5) card_57 = calc11_card_1992 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1993_eq : placed 4 (7, 5) card_111 = calc11_card_1993 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1994_eq : placed 3 (10, 7) card_390 = calc11_card_1994 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1995_eq : placed 0 (4, 5) card_397 = calc11_card_1995 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1996_eq : calc11_card_1995.required ∪ ∅ = calc11_set_1996 := by decide +kernel

theorem calc11_set_1997_eq : calc11_card_1995.envelope ∪ ∅ = calc11_set_1997 := by decide +kernel

theorem calc11_set_1998_eq : calc11_card_1994.required ∪ calc11_set_1996 = calc11_set_1998 := by decide +kernel

theorem calc11_set_1999_eq : calc11_card_1994.envelope ∪ calc11_set_1997 = calc11_set_1999 := by decide +kernel

theorem calc11_set_2000_eq : calc11_card_1993.required ∪ calc11_set_1998 = calc11_set_2000 := by decide +kernel

theorem calc11_set_2001_eq : calc11_card_1993.envelope ∪ calc11_set_1999 = calc11_set_2001 := by decide +kernel

theorem calc11_set_2002_eq : calc11_card_1992.required ∪ calc11_set_2000 = calc11_set_2002 := by decide +kernel

theorem calc11_set_2003_eq : calc11_card_1992.envelope ∪ calc11_set_2001 = calc11_set_2003 := by decide +kernel

theorem calc11_set_2004_eq : calc11_card_1995.envelope ∩ calc11_card_1992.envelope = calc11_set_2004 := by decide +kernel

theorem calc11_set_2005_eq : calc11_card_1994.envelope ∩ calc11_set_2004 = calc11_set_2005 := by decide +kernel

theorem calc11_set_2006_eq : calc11_card_1993.envelope ∩ calc11_set_2005 = calc11_set_2006 := by decide +kernel

theorem calc11_set_2007_eq : calc11_set_2002 ∪ calc11_set_2006 = calc11_set_2007 := by decide +kernel

theorem calc11_finishA_2008 : calc11_set_2007.erase (4, 8) = inline_889.required := by decide +kernel

theorem calc11_finishT_2008 : insert (4, 8) calc11_set_2003 = inline_889.envelope := by decide +kernel

theorem eq_inline_889 : inline_889 = combine (4, 8) [placed 0 (3, 5) card_57, placed 4 (7, 5) card_111, placed 3 (10, 7) card_390, placed 0 (4, 5) card_397] := by
  rw [calc11_card_1992_eq, calc11_card_1993_eq, calc11_card_1994_eq, calc11_card_1995_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1996_eq, calc11_set_1998_eq, calc11_set_2000_eq, calc11_set_2002_eq, calc11_set_2004_eq, calc11_set_2005_eq, calc11_set_2006_eq, calc11_set_2007_eq, calc11_finishA_2008]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1997_eq, calc11_set_1999_eq, calc11_set_2001_eq, calc11_set_2003_eq, calc11_finishT_2008]
  · decide +kernel

theorem valid_inline_889 : Valid inline_889 := by
  rw [eq_inline_889]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 5) valid_57
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_111
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 7) valid_390
  subst c
  exact placed_valid 0 (4, 5) valid_397

theorem calc11_card_2009_eq : placed 3 (8, 7) card_19 = calc11_card_2009 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2010_eq : placed 7 (8, 9) card_19 = calc11_card_2010 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2011_eq : placed 0 (4, 6) card_395 = calc11_card_2011 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2012_eq : calc11_card_2011.required ∪ ∅ = calc11_set_2012 := by decide +kernel

theorem calc11_set_2013_eq : calc11_card_2011.envelope ∪ ∅ = calc11_set_2013 := by decide +kernel

theorem calc11_set_2014_eq : calc11_card_2010.required ∪ calc11_set_2012 = calc11_set_2014 := by decide +kernel

theorem calc11_set_2015_eq : calc11_card_2010.envelope ∪ calc11_set_2013 = calc11_set_2015 := by decide +kernel

theorem calc11_set_2016_eq : calc11_card_2009.required ∪ calc11_set_2014 = calc11_set_2016 := by decide +kernel

theorem calc11_set_2017_eq : calc11_card_2009.envelope ∪ calc11_set_2015 = calc11_set_2017 := by decide +kernel

theorem calc11_set_2018_eq : calc11_card_2011.envelope ∩ calc11_card_2009.envelope = calc11_set_2018 := by decide +kernel

theorem calc11_set_2019_eq : calc11_card_2010.envelope ∩ calc11_set_2018 = calc11_set_2019 := by decide +kernel

theorem calc11_set_2020_eq : calc11_set_2016 ∪ calc11_set_2019 = calc11_set_2020 := by decide +kernel

theorem calc11_finishA_2021 : calc11_set_2020.erase (4, 8) = inline_890.required := by decide +kernel

theorem calc11_finishT_2021 : insert (4, 8) calc11_set_2017 = inline_890.envelope := by decide +kernel

theorem eq_inline_890 : inline_890 = combine (4, 8) [placed 3 (8, 7) card_19, placed 7 (8, 9) card_19, placed 0 (4, 6) card_395] := by
  rw [calc11_card_2009_eq, calc11_card_2010_eq, calc11_card_2011_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2012_eq, calc11_set_2014_eq, calc11_set_2016_eq, calc11_set_2018_eq, calc11_set_2019_eq, calc11_set_2020_eq, calc11_finishA_2021]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2013_eq, calc11_set_2015_eq, calc11_set_2017_eq, calc11_finishT_2021]
  · decide +kernel

theorem valid_inline_890 : Valid inline_890 := by
  rw [eq_inline_890]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 7) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 9) valid_19
  subst c
  exact placed_valid 0 (4, 6) valid_395

theorem calc11_card_2022_eq : placed 3 (8, 7) card_19 = calc11_card_2022 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2023_eq : placed 4 (7, 5) card_231 = calc11_card_2023 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2024_eq : placed 0 (4, 5) card_279 = calc11_card_2024 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2025_eq : calc11_card_2024.required ∪ ∅ = calc11_set_2025 := by decide +kernel

theorem calc11_set_2026_eq : calc11_card_2024.envelope ∪ ∅ = calc11_set_2026 := by decide +kernel

theorem calc11_set_2027_eq : calc11_card_2023.required ∪ calc11_set_2025 = calc11_set_2027 := by decide +kernel

theorem calc11_set_2028_eq : calc11_card_2023.envelope ∪ calc11_set_2026 = calc11_set_2028 := by decide +kernel

theorem calc11_set_2029_eq : calc11_card_2022.required ∪ calc11_set_2027 = calc11_set_2029 := by decide +kernel

theorem calc11_set_2030_eq : calc11_card_2022.envelope ∪ calc11_set_2028 = calc11_set_2030 := by decide +kernel

theorem calc11_set_2031_eq : calc11_card_2024.envelope ∩ calc11_card_2022.envelope = calc11_set_2031 := by decide +kernel

theorem calc11_set_2032_eq : calc11_card_2023.envelope ∩ calc11_set_2031 = calc11_set_2032 := by decide +kernel

theorem calc11_set_2033_eq : calc11_set_2029 ∪ calc11_set_2032 = calc11_set_2033 := by decide +kernel

theorem calc11_finishA_2034 : calc11_set_2033.erase (4, 8) = inline_891.required := by decide +kernel

theorem calc11_finishT_2034 : insert (4, 8) calc11_set_2030 = inline_891.envelope := by decide +kernel

theorem eq_inline_891 : inline_891 = combine (4, 8) [placed 3 (8, 7) card_19, placed 4 (7, 5) card_231, placed 0 (4, 5) card_279] := by
  rw [calc11_card_2022_eq, calc11_card_2023_eq, calc11_card_2024_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2025_eq, calc11_set_2027_eq, calc11_set_2029_eq, calc11_set_2031_eq, calc11_set_2032_eq, calc11_set_2033_eq, calc11_finishA_2034]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2026_eq, calc11_set_2028_eq, calc11_set_2030_eq, calc11_finishT_2034]
  · decide +kernel

theorem valid_inline_891 : Valid inline_891 := by
  rw [eq_inline_891]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 7) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_231
  subst c
  exact placed_valid 0 (4, 5) valid_279

theorem calc11_card_2035_eq : placed 6 (6, 11) card_53 = calc11_card_2035 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2036_eq : placed 0 (4, 6) card_637 = calc11_card_2036 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2037_eq : calc11_card_2036.required ∪ ∅ = calc11_set_2037 := by decide +kernel

theorem calc11_set_2038_eq : calc11_card_2036.envelope ∪ ∅ = calc11_set_2038 := by decide +kernel

theorem calc11_set_2039_eq : calc11_card_2035.required ∪ calc11_set_2037 = calc11_set_2039 := by decide +kernel

theorem calc11_set_2040_eq : calc11_card_2035.envelope ∪ calc11_set_2038 = calc11_set_2040 := by decide +kernel

theorem calc11_set_2041_eq : calc11_card_2036.envelope ∩ calc11_card_2035.envelope = calc11_set_2041 := by decide +kernel

theorem calc11_set_2042_eq : calc11_set_2039 ∪ calc11_set_2041 = calc11_set_2042 := by decide +kernel

theorem calc11_finishA_2043 : calc11_set_2042.erase (6, 9) = inline_892.required := by decide +kernel

theorem calc11_finishT_2043 : insert (6, 9) calc11_set_2040 = inline_892.envelope := by decide +kernel

theorem eq_inline_892 : inline_892 = combine (6, 9) [placed 6 (6, 11) card_53, placed 0 (4, 6) card_637] := by
  rw [calc11_card_2035_eq, calc11_card_2036_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2037_eq, calc11_set_2039_eq, calc11_set_2041_eq, calc11_set_2042_eq, calc11_finishA_2043]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2038_eq, calc11_set_2040_eq, calc11_finishT_2043]
  · decide +kernel

theorem valid_inline_892 : Valid inline_892 := by
  rw [eq_inline_892]
  apply combination_rule (6, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 11) valid_53
  subst c
  exact placed_valid 0 (4, 6) valid_637

theorem calc11_card_2044_eq : placed 1 (3, 6) card_188 = calc11_card_2044 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2045_eq : placed 5 (3, 10) card_188 = calc11_card_2045 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2046_eq : placed 0 (5, 5) card_258 = calc11_card_2046 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2047_eq : inline_892.required ∪ ∅ = calc11_set_2047 := by decide +kernel

theorem calc11_set_2048_eq : inline_892.envelope ∪ ∅ = calc11_set_2048 := by decide +kernel

theorem calc11_set_2049_eq : inline_891.required ∪ calc11_set_2047 = calc11_set_2049 := by decide +kernel

theorem calc11_set_2050_eq : inline_891.envelope ∪ calc11_set_2048 = calc11_set_2050 := by decide +kernel

theorem calc11_set_2051_eq : inline_890.required ∪ calc11_set_2049 = calc11_set_2051 := by decide +kernel

theorem calc11_set_2052_eq : inline_890.envelope ∪ calc11_set_2050 = calc11_set_2052 := by decide +kernel

theorem calc11_set_2053_eq : calc11_card_2046.required ∪ calc11_set_2051 = calc11_set_2053 := by decide +kernel

theorem calc11_set_2054_eq : calc11_card_2046.envelope ∪ calc11_set_2052 = calc11_set_2054 := by decide +kernel

theorem calc11_set_2055_eq : calc11_card_2045.required ∪ calc11_set_2053 = calc11_set_2055 := by decide +kernel

theorem calc11_set_2056_eq : calc11_card_2045.envelope ∪ calc11_set_2054 = calc11_set_2056 := by decide +kernel

theorem calc11_set_2057_eq : calc11_card_2044.required ∪ calc11_set_2055 = calc11_set_2057 := by decide +kernel

theorem calc11_set_2058_eq : calc11_card_2044.envelope ∪ calc11_set_2056 = calc11_set_2058 := by decide +kernel

theorem calc11_set_2059_eq : inline_892.envelope ∩ calc11_card_2044.envelope = calc11_set_2059 := by decide +kernel

theorem calc11_set_2060_eq : inline_891.envelope ∩ calc11_set_2059 = calc11_set_2060 := by decide +kernel

theorem calc11_set_2061_eq : inline_890.envelope ∩ calc11_set_2060 = calc11_set_2061 := by decide +kernel

theorem calc11_set_2062_eq : calc11_card_2046.envelope ∩ calc11_set_2061 = calc11_set_2062 := by decide +kernel

theorem calc11_set_2063_eq : calc11_card_2045.envelope ∩ calc11_set_2062 = calc11_set_2063 := by decide +kernel

theorem calc11_set_2064_eq : calc11_set_2057 ∪ calc11_set_2063 = calc11_set_2064 := by decide +kernel

theorem calc11_finishA_2065 : calc11_set_2064.erase (7, 8) = inline_893.required := by decide +kernel

theorem calc11_finishT_2065 : insert (7, 8) calc11_set_2058 = inline_893.envelope := by decide +kernel

theorem eq_inline_893 : inline_893 = combine (7, 8) [placed 1 (3, 6) card_188, placed 5 (3, 10) card_188, placed 0 (5, 5) card_258, inline_890, inline_891, inline_892] := by
  rw [calc11_card_2044_eq, calc11_card_2045_eq, calc11_card_2046_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2047_eq, calc11_set_2049_eq, calc11_set_2051_eq, calc11_set_2053_eq, calc11_set_2055_eq, calc11_set_2057_eq, calc11_set_2059_eq, calc11_set_2060_eq, calc11_set_2061_eq, calc11_set_2062_eq, calc11_set_2063_eq, calc11_set_2064_eq, calc11_finishA_2065]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2048_eq, calc11_set_2050_eq, calc11_set_2052_eq, calc11_set_2054_eq, calc11_set_2056_eq, calc11_set_2058_eq, calc11_finishT_2065]
  · decide +kernel

theorem valid_inline_893 : Valid inline_893 := by
  rw [eq_inline_893]
  apply combination_rule (7, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 6) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 10) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 5) valid_258
  rcases hc with rfl | hc
  · exact valid_inline_890
  rcases hc with rfl | hc
  · exact valid_inline_891
  subst c
  exact valid_inline_892

theorem calc11_card_2066_eq : placed 7 (8, 8) card_53 = calc11_card_2066 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2067_eq : placed 1 (2, 7) card_53 = calc11_card_2067 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2068_eq : placed 7 (10, 12) card_720 = calc11_card_2068 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2069_eq : placed 1 (0, 3) card_720 = calc11_card_2069 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2070_eq : calc11_card_2069.required ∪ ∅ = calc11_set_2070 := by decide +kernel

theorem calc11_set_2071_eq : calc11_card_2069.envelope ∪ ∅ = calc11_set_2071 := by decide +kernel

theorem calc11_set_2072_eq : calc11_card_2068.required ∪ calc11_set_2070 = calc11_set_2072 := by decide +kernel

theorem calc11_set_2073_eq : calc11_card_2068.envelope ∪ calc11_set_2071 = calc11_set_2073 := by decide +kernel

theorem calc11_set_2074_eq : calc11_card_2067.required ∪ calc11_set_2072 = calc11_set_2074 := by decide +kernel

theorem calc11_set_2075_eq : calc11_card_2067.envelope ∪ calc11_set_2073 = calc11_set_2075 := by decide +kernel

theorem calc11_set_2076_eq : calc11_card_2066.required ∪ calc11_set_2074 = calc11_set_2076 := by decide +kernel

theorem calc11_set_2077_eq : calc11_card_2066.envelope ∪ calc11_set_2075 = calc11_set_2077 := by decide +kernel

theorem calc11_set_2078_eq : calc11_card_2069.envelope ∩ calc11_card_2066.envelope = calc11_set_2078 := by decide +kernel

theorem calc11_set_2079_eq : calc11_card_2068.envelope ∩ calc11_set_2078 = calc11_set_2079 := by decide +kernel

theorem calc11_set_2080_eq : calc11_card_2067.envelope ∩ calc11_set_2079 = calc11_set_2080 := by decide +kernel

theorem calc11_set_2081_eq : calc11_set_2076 ∪ calc11_set_2080 = calc11_set_2081 := by decide +kernel

theorem calc11_finishA_2082 : calc11_set_2081.erase (4, 7) = inline_894.required := by decide +kernel

theorem calc11_finishT_2082 : insert (4, 7) calc11_set_2077 = inline_894.envelope := by decide +kernel

theorem eq_inline_894 : inline_894 = combine (4, 7) [placed 7 (8, 8) card_53, placed 1 (2, 7) card_53, placed 7 (10, 12) card_720, placed 1 (0, 3) card_720] := by
  rw [calc11_card_2066_eq, calc11_card_2067_eq, calc11_card_2068_eq, calc11_card_2069_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2070_eq, calc11_set_2072_eq, calc11_set_2074_eq, calc11_set_2076_eq, calc11_set_2078_eq, calc11_set_2079_eq, calc11_set_2080_eq, calc11_set_2081_eq, calc11_finishA_2082]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2071_eq, calc11_set_2073_eq, calc11_set_2075_eq, calc11_set_2077_eq, calc11_finishT_2082]
  · decide +kernel

theorem valid_inline_894 : Valid inline_894 := by
  rw [eq_inline_894]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 8) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 7) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 7 (10, 12) valid_720
  subst c
  exact placed_valid 1 (0, 3) valid_720

theorem calc11_card_2083_eq : placed 0 (4, 4) card_512 = calc11_card_2083 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2084_eq : placed 5 (2, 10) card_600 = calc11_card_2084 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2085_eq : placed 6 (9, 11) card_621 = calc11_card_2085 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2086_eq : placed 1 (3, 6) card_702 = calc11_card_2086 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2087_eq : placed 4 (8, 3) card_714 = calc11_card_2087 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2088_eq : calc11_card_2087.required ∪ ∅ = calc11_set_2088 := by decide +kernel

theorem calc11_set_2089_eq : calc11_card_2087.envelope ∪ ∅ = calc11_set_2089 := by decide +kernel

theorem calc11_set_2090_eq : calc11_card_2086.required ∪ calc11_set_2088 = calc11_set_2090 := by decide +kernel

theorem calc11_set_2091_eq : calc11_card_2086.envelope ∪ calc11_set_2089 = calc11_set_2091 := by decide +kernel

theorem calc11_set_2092_eq : calc11_card_2085.required ∪ calc11_set_2090 = calc11_set_2092 := by decide +kernel

theorem calc11_set_2093_eq : calc11_card_2085.envelope ∪ calc11_set_2091 = calc11_set_2093 := by decide +kernel

theorem calc11_set_2094_eq : calc11_card_2084.required ∪ calc11_set_2092 = calc11_set_2094 := by decide +kernel

theorem calc11_set_2095_eq : calc11_card_2084.envelope ∪ calc11_set_2093 = calc11_set_2095 := by decide +kernel

theorem calc11_set_2096_eq : calc11_card_2083.required ∪ calc11_set_2094 = calc11_set_2096 := by decide +kernel

theorem calc11_set_2097_eq : calc11_card_2083.envelope ∪ calc11_set_2095 = calc11_set_2097 := by decide +kernel

theorem calc11_set_2098_eq : calc11_card_2087.envelope ∩ calc11_card_2083.envelope = calc11_set_2098 := by decide +kernel

theorem calc11_set_2099_eq : calc11_card_2086.envelope ∩ calc11_set_2098 = calc11_set_2099 := by decide +kernel

theorem calc11_set_2100_eq : calc11_card_2085.envelope ∩ calc11_set_2099 = calc11_set_2100 := by decide +kernel

theorem calc11_set_2101_eq : calc11_card_2084.envelope ∩ calc11_set_2100 = calc11_set_2101 := by decide +kernel

theorem calc11_set_2102_eq : calc11_set_2096 ∪ calc11_set_2101 = calc11_set_2102 := by decide +kernel

theorem calc11_finishA_2103 : calc11_set_2102.erase (6, 7) = inline_895.required := by decide +kernel

theorem calc11_finishT_2103 : insert (6, 7) calc11_set_2097 = inline_895.envelope := by decide +kernel

theorem eq_inline_895 : inline_895 = combine (6, 7) [placed 0 (4, 4) card_512, placed 5 (2, 10) card_600, placed 6 (9, 11) card_621, placed 1 (3, 6) card_702, placed 4 (8, 3) card_714] := by
  rw [calc11_card_2083_eq, calc11_card_2084_eq, calc11_card_2085_eq, calc11_card_2086_eq, calc11_card_2087_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2088_eq, calc11_set_2090_eq, calc11_set_2092_eq, calc11_set_2094_eq, calc11_set_2096_eq, calc11_set_2098_eq, calc11_set_2099_eq, calc11_set_2100_eq, calc11_set_2101_eq, calc11_set_2102_eq, calc11_finishA_2103]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2089_eq, calc11_set_2091_eq, calc11_set_2093_eq, calc11_set_2095_eq, calc11_set_2097_eq, calc11_finishT_2103]
  · decide +kernel

theorem valid_inline_895 : Valid inline_895 := by
  rw [eq_inline_895]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_512
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 10) valid_600
  rcases hc with rfl | hc
  · exact placed_valid 6 (9, 11) valid_621
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 6) valid_702
  subst c
  exact placed_valid 4 (8, 3) valid_714

theorem calc11_card_2104_eq : placed 5 (3, 8) card_7 = calc11_card_2104 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2105_eq : placed 1 (3, 7) card_9 = calc11_card_2105 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2106_eq : placed 0 (4, 5) card_604 = calc11_card_2106 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2107_eq : calc11_card_2106.required ∪ ∅ = calc11_set_2107 := by decide +kernel

theorem calc11_set_2108_eq : calc11_card_2106.envelope ∪ ∅ = calc11_set_2108 := by decide +kernel

theorem calc11_set_2109_eq : calc11_card_2105.required ∪ calc11_set_2107 = calc11_set_2109 := by decide +kernel

theorem calc11_set_2110_eq : calc11_card_2105.envelope ∪ calc11_set_2108 = calc11_set_2110 := by decide +kernel

theorem calc11_set_2111_eq : calc11_card_2104.required ∪ calc11_set_2109 = calc11_set_2111 := by decide +kernel

theorem calc11_set_2112_eq : calc11_card_2104.envelope ∪ calc11_set_2110 = calc11_set_2112 := by decide +kernel

theorem calc11_set_2113_eq : calc11_card_2106.envelope ∩ calc11_card_2104.envelope = calc11_set_2113 := by decide +kernel

theorem calc11_set_2114_eq : calc11_card_2105.envelope ∩ calc11_set_2113 = calc11_set_2114 := by decide +kernel

theorem calc11_set_2115_eq : calc11_set_2111 ∪ calc11_set_2114 = calc11_set_2115 := by decide +kernel

theorem calc11_finishA_2116 : calc11_set_2115.erase (7, 8) = inline_896.required := by decide +kernel

theorem calc11_finishT_2116 : insert (7, 8) calc11_set_2112 = inline_896.envelope := by decide +kernel

theorem eq_inline_896 : inline_896 = combine (7, 8) [placed 5 (3, 8) card_7, placed 1 (3, 7) card_9, placed 0 (4, 5) card_604] := by
  rw [calc11_card_2104_eq, calc11_card_2105_eq, calc11_card_2106_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2107_eq, calc11_set_2109_eq, calc11_set_2111_eq, calc11_set_2113_eq, calc11_set_2114_eq, calc11_set_2115_eq, calc11_finishA_2116]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2108_eq, calc11_set_2110_eq, calc11_set_2112_eq, calc11_finishT_2116]
  · decide +kernel

theorem valid_inline_896 : Valid inline_896 := by
  rw [eq_inline_896]
  apply combination_rule (7, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 7) valid_9
  subst c
  exact placed_valid 0 (4, 5) valid_604

theorem calc11_card_2117_eq : placed 0 (3, 5) card_88 = calc11_card_2117 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2118_eq : placed 4 (7, 5) card_231 = calc11_card_2118 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2119_eq : placed 3 (8, 6) card_267 = calc11_card_2119 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2120_eq : inline_896.required ∪ ∅ = calc11_set_2120 := by decide +kernel

theorem calc11_set_2121_eq : inline_896.envelope ∪ ∅ = calc11_set_2121 := by decide +kernel

theorem calc11_set_2122_eq : calc11_card_2119.required ∪ calc11_set_2120 = calc11_set_2122 := by decide +kernel

theorem calc11_set_2123_eq : calc11_card_2119.envelope ∪ calc11_set_2121 = calc11_set_2123 := by decide +kernel

theorem calc11_set_2124_eq : calc11_card_2118.required ∪ calc11_set_2122 = calc11_set_2124 := by decide +kernel

theorem calc11_set_2125_eq : calc11_card_2118.envelope ∪ calc11_set_2123 = calc11_set_2125 := by decide +kernel

theorem calc11_set_2126_eq : calc11_card_2117.required ∪ calc11_set_2124 = calc11_set_2126 := by decide +kernel

theorem calc11_set_2127_eq : calc11_card_2117.envelope ∪ calc11_set_2125 = calc11_set_2127 := by decide +kernel

theorem calc11_set_2128_eq : inline_896.envelope ∩ calc11_card_2117.envelope = calc11_set_2128 := by decide +kernel

theorem calc11_set_2129_eq : calc11_card_2119.envelope ∩ calc11_set_2128 = calc11_set_2129 := by decide +kernel

theorem calc11_set_2130_eq : calc11_card_2118.envelope ∩ calc11_set_2129 = calc11_set_2130 := by decide +kernel

theorem calc11_set_2131_eq : calc11_set_2126 ∪ calc11_set_2130 = calc11_set_2131 := by decide +kernel

theorem calc11_finishA_2132 : calc11_set_2131.erase (4, 8) = inline_897.required := by decide +kernel

theorem calc11_finishT_2132 : insert (4, 8) calc11_set_2127 = inline_897.envelope := by decide +kernel

theorem eq_inline_897 : inline_897 = combine (4, 8) [placed 0 (3, 5) card_88, placed 4 (7, 5) card_231, placed 3 (8, 6) card_267, inline_896] := by
  rw [calc11_card_2117_eq, calc11_card_2118_eq, calc11_card_2119_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2120_eq, calc11_set_2122_eq, calc11_set_2124_eq, calc11_set_2126_eq, calc11_set_2128_eq, calc11_set_2129_eq, calc11_set_2130_eq, calc11_set_2131_eq, calc11_finishA_2132]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2121_eq, calc11_set_2123_eq, calc11_set_2125_eq, calc11_set_2127_eq, calc11_finishT_2132]
  · decide +kernel

theorem valid_inline_897 : Valid inline_897 := by
  rw [eq_inline_897]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 5) valid_88
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_231
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 6) valid_267
  subst c
  exact valid_inline_896

theorem calc11_card_2133_eq : placed 3 (9, 5) card_523 = calc11_card_2133 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2134_eq : placed 3 (9, 5) card_524 = calc11_card_2134 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2135_eq : placed 1 (1, 5) card_677 = calc11_card_2135 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2136_eq : placed 7 (10, 10) card_719 = calc11_card_2136 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2137_eq : placed 6 (8, 13) card_723 = calc11_card_2137 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2138_eq : calc11_card_2137.required ∪ ∅ = calc11_set_2138 := by decide +kernel

theorem calc11_set_2139_eq : calc11_card_2137.envelope ∪ ∅ = calc11_set_2139 := by decide +kernel

theorem calc11_set_2140_eq : inline_897.required ∪ calc11_set_2138 = calc11_set_2140 := by decide +kernel

theorem calc11_set_2141_eq : inline_897.envelope ∪ calc11_set_2139 = calc11_set_2141 := by decide +kernel

theorem calc11_set_2142_eq : inline_895.required ∪ calc11_set_2140 = calc11_set_2142 := by decide +kernel

theorem calc11_set_2143_eq : inline_895.envelope ∪ calc11_set_2141 = calc11_set_2143 := by decide +kernel

theorem calc11_set_2144_eq : inline_894.required ∪ calc11_set_2142 = calc11_set_2144 := by decide +kernel

theorem calc11_set_2145_eq : inline_894.envelope ∪ calc11_set_2143 = calc11_set_2145 := by decide +kernel

theorem calc11_set_2146_eq : calc11_card_2136.required ∪ calc11_set_2144 = calc11_set_2146 := by decide +kernel

theorem calc11_set_2147_eq : calc11_card_2136.envelope ∪ calc11_set_2145 = calc11_set_2147 := by decide +kernel

theorem calc11_set_2148_eq : inline_893.required ∪ calc11_set_2146 = calc11_set_2148 := by decide +kernel

theorem calc11_set_2149_eq : inline_893.envelope ∪ calc11_set_2147 = calc11_set_2149 := by decide +kernel

theorem calc11_set_2150_eq : inline_889.required ∪ calc11_set_2148 = calc11_set_2150 := by decide +kernel

theorem calc11_set_2151_eq : inline_889.envelope ∪ calc11_set_2149 = calc11_set_2151 := by decide +kernel

theorem calc11_set_2152_eq : calc11_card_2135.required ∪ calc11_set_2150 = calc11_set_2152 := by decide +kernel

theorem calc11_set_2153_eq : calc11_card_2135.envelope ∪ calc11_set_2151 = calc11_set_2153 := by decide +kernel

theorem calc11_set_2154_eq : calc11_card_2134.required ∪ calc11_set_2152 = calc11_set_2154 := by decide +kernel

theorem calc11_set_2155_eq : calc11_card_2134.envelope ∪ calc11_set_2153 = calc11_set_2155 := by decide +kernel

theorem calc11_set_2156_eq : calc11_card_2133.required ∪ calc11_set_2154 = calc11_set_2156 := by decide +kernel

theorem calc11_set_2157_eq : calc11_card_2133.envelope ∪ calc11_set_2155 = calc11_set_2157 := by decide +kernel

theorem calc11_set_2158_eq : calc11_card_2137.envelope ∩ calc11_card_2133.envelope = calc11_set_2158 := by decide +kernel

theorem calc11_set_2159_eq : inline_897.envelope ∩ calc11_set_2158 = calc11_set_2159 := by decide +kernel

theorem calc11_set_2160_eq : inline_895.envelope ∩ calc11_set_2159 = calc11_set_2160 := by decide +kernel

theorem calc11_set_2161_eq : inline_894.envelope ∩ calc11_set_2160 = calc11_set_2161 := by decide +kernel

theorem calc11_set_2162_eq : calc11_card_2136.envelope ∩ calc11_set_2161 = calc11_set_2162 := by decide +kernel

theorem calc11_set_2163_eq : inline_893.envelope ∩ calc11_set_2162 = calc11_set_2163 := by decide +kernel

theorem calc11_set_2164_eq : inline_889.envelope ∩ calc11_set_2163 = calc11_set_2164 := by decide +kernel

theorem calc11_set_2165_eq : calc11_card_2135.envelope ∩ calc11_set_2164 = calc11_set_2165 := by decide +kernel

theorem calc11_set_2166_eq : calc11_card_2134.envelope ∩ calc11_set_2165 = calc11_set_2166 := by decide +kernel

theorem calc11_set_2167_eq : calc11_set_2156 ∪ calc11_set_2166 = calc11_set_2167 := by decide +kernel

theorem calc11_finishA_2168 : calc11_set_2167.erase (6, 8) = card_724.required := by decide +kernel

theorem calc11_finishT_2168 : insert (6, 8) calc11_set_2157 = card_724.envelope := by decide +kernel

theorem eq_card_724 : card_724 = combine (6, 8) [placed 3 (9, 5) card_523, placed 3 (9, 5) card_524, placed 1 (1, 5) card_677, inline_889, inline_893, placed 7 (10, 10) card_719, inline_894, inline_895, inline_897, placed 6 (8, 13) card_723] := by
  rw [calc11_card_2133_eq, calc11_card_2134_eq, calc11_card_2135_eq, calc11_card_2136_eq, calc11_card_2137_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2138_eq, calc11_set_2140_eq, calc11_set_2142_eq, calc11_set_2144_eq, calc11_set_2146_eq, calc11_set_2148_eq, calc11_set_2150_eq, calc11_set_2152_eq, calc11_set_2154_eq, calc11_set_2156_eq, calc11_set_2158_eq, calc11_set_2159_eq, calc11_set_2160_eq, calc11_set_2161_eq, calc11_set_2162_eq, calc11_set_2163_eq, calc11_set_2164_eq, calc11_set_2165_eq, calc11_set_2166_eq, calc11_set_2167_eq, calc11_finishA_2168]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2139_eq, calc11_set_2141_eq, calc11_set_2143_eq, calc11_set_2145_eq, calc11_set_2147_eq, calc11_set_2149_eq, calc11_set_2151_eq, calc11_set_2153_eq, calc11_set_2155_eq, calc11_set_2157_eq, calc11_finishT_2168]
  · decide +kernel

theorem valid_724 : Valid card_724 := by
  rw [eq_card_724]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 5) valid_523
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 5) valid_524
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 5) valid_677
  rcases hc with rfl | hc
  · exact valid_inline_889
  rcases hc with rfl | hc
  · exact valid_inline_893
  rcases hc with rfl | hc
  · exact placed_valid 7 (10, 10) valid_719
  rcases hc with rfl | hc
  · exact valid_inline_894
  rcases hc with rfl | hc
  · exact valid_inline_895
  rcases hc with rfl | hc
  · exact valid_inline_897
  subst c
  exact placed_valid 6 (8, 13) valid_723

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

theorem calc11_card_2234_eq : placed 1 (3, 6) card_459 = calc11_card_2234 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2235_eq : placed 2 (6, 11) card_579 = calc11_card_2235 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2236_eq : placed 1 (3, 3) card_581 = calc11_card_2236 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2237_eq : placed 1 (4, 4) card_654 = calc11_card_2237 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2238_eq : placed 3 (12, 3) card_661 = calc11_card_2238 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2239_eq : placed 5 (3, 10) card_677 = calc11_card_2239 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2240_eq : placed 2 (4, 12) card_682 = calc11_card_2240 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2241_eq : placed 1 (2, 2) card_694 = calc11_card_2241 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2242_eq : placed 3 (13, 2) card_696 = calc11_card_2242 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2243_eq : placed 5 (3, 11) card_698 = calc11_card_2243 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2244_eq : placed 3 (13, 2) card_709 = calc11_card_2244 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2245_eq : placed 3 (12, 4) card_710 = calc11_card_2245 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2246_eq : placed 0 (3, 2) card_715 = calc11_card_2246 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2247_eq : placed 2 (3, 13) card_717 = calc11_card_2247 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2248_eq : placed 3 (13, 2) card_718 = calc11_card_2248 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2249_eq : placed 3 (15, 2) card_724 = calc11_card_2249 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2250_eq : calc11_card_2249.required ∪ ∅ = calc11_set_2250 := by decide +kernel

theorem calc11_set_2251_eq : calc11_card_2249.envelope ∪ ∅ = calc11_set_2251 := by decide +kernel

theorem calc11_set_2252_eq : calc11_card_2248.required ∪ calc11_set_2250 = calc11_set_2252 := by decide +kernel

theorem calc11_set_2253_eq : calc11_card_2248.envelope ∪ calc11_set_2251 = calc11_set_2253 := by decide +kernel

theorem calc11_set_2254_eq : calc11_card_2247.required ∪ calc11_set_2252 = calc11_set_2254 := by decide +kernel

theorem calc11_set_2255_eq : calc11_card_2247.envelope ∪ calc11_set_2253 = calc11_set_2255 := by decide +kernel

theorem calc11_set_2256_eq : calc11_card_2246.required ∪ calc11_set_2254 = calc11_set_2256 := by decide +kernel

theorem calc11_set_2257_eq : calc11_card_2246.envelope ∪ calc11_set_2255 = calc11_set_2257 := by decide +kernel

theorem calc11_set_2258_eq : calc11_card_2245.required ∪ calc11_set_2256 = calc11_set_2258 := by decide +kernel

theorem calc11_set_2259_eq : calc11_card_2245.envelope ∪ calc11_set_2257 = calc11_set_2259 := by decide +kernel

theorem calc11_set_2260_eq : calc11_card_2244.required ∪ calc11_set_2258 = calc11_set_2260 := by decide +kernel

theorem calc11_set_2261_eq : calc11_card_2244.envelope ∪ calc11_set_2259 = calc11_set_2261 := by decide +kernel

theorem calc11_set_2262_eq : calc11_card_2243.required ∪ calc11_set_2260 = calc11_set_2262 := by decide +kernel

theorem calc11_set_2263_eq : calc11_card_2243.envelope ∪ calc11_set_2261 = calc11_set_2263 := by decide +kernel

theorem calc11_set_2264_eq : calc11_card_2242.required ∪ calc11_set_2262 = calc11_set_2264 := by decide +kernel

theorem calc11_set_2265_eq : calc11_card_2242.envelope ∪ calc11_set_2263 = calc11_set_2265 := by decide +kernel

theorem calc11_set_2266_eq : calc11_card_2241.required ∪ calc11_set_2264 = calc11_set_2266 := by decide +kernel

theorem calc11_set_2267_eq : calc11_card_2241.envelope ∪ calc11_set_2265 = calc11_set_2267 := by decide +kernel

theorem calc11_set_2268_eq : calc11_card_2240.required ∪ calc11_set_2266 = calc11_set_2268 := by decide +kernel

theorem calc11_set_2269_eq : calc11_card_2240.envelope ∪ calc11_set_2267 = calc11_set_2269 := by decide +kernel

theorem calc11_set_2270_eq : calc11_card_2239.required ∪ calc11_set_2268 = calc11_set_2270 := by decide +kernel

theorem calc11_set_2271_eq : calc11_card_2239.envelope ∪ calc11_set_2269 = calc11_set_2271 := by decide +kernel

theorem calc11_set_2272_eq : calc11_card_2238.required ∪ calc11_set_2270 = calc11_set_2272 := by decide +kernel

theorem calc11_set_2273_eq : calc11_card_2238.envelope ∪ calc11_set_2271 = calc11_set_2273 := by decide +kernel

theorem calc11_set_2274_eq : calc11_card_2237.required ∪ calc11_set_2272 = calc11_set_2274 := by decide +kernel

theorem calc11_set_2275_eq : calc11_card_2237.envelope ∪ calc11_set_2273 = calc11_set_2275 := by decide +kernel

theorem calc11_set_2276_eq : calc11_card_2236.required ∪ calc11_set_2274 = calc11_set_2276 := by decide +kernel

theorem calc11_set_2277_eq : calc11_card_2236.envelope ∪ calc11_set_2275 = calc11_set_2277 := by decide +kernel

theorem calc11_set_2278_eq : calc11_card_2235.required ∪ calc11_set_2276 = calc11_set_2278 := by decide +kernel

theorem calc11_set_2279_eq : calc11_card_2235.envelope ∪ calc11_set_2277 = calc11_set_2279 := by decide +kernel

theorem calc11_set_2280_eq : calc11_card_2234.required ∪ calc11_set_2278 = calc11_set_2280 := by decide +kernel

theorem calc11_set_2281_eq : calc11_card_2234.envelope ∪ calc11_set_2279 = calc11_set_2281 := by decide +kernel

theorem calc11_set_2282_eq : calc11_card_2249.envelope ∩ calc11_card_2234.envelope = calc11_set_2282 := by decide +kernel

theorem calc11_set_2283_eq : calc11_card_2248.envelope ∩ calc11_set_2282 = calc11_set_2283 := by decide +kernel

theorem calc11_set_2284_eq : calc11_card_2247.envelope ∩ calc11_set_2283 = calc11_set_2284 := by decide +kernel

theorem calc11_set_2285_eq : calc11_card_2246.envelope ∩ calc11_set_2284 = calc11_set_2285 := by decide +kernel

theorem calc11_set_2286_eq : calc11_card_2245.envelope ∩ calc11_set_2285 = calc11_set_2286 := by decide +kernel

theorem calc11_set_2287_eq : calc11_card_2244.envelope ∩ calc11_set_2286 = calc11_set_2287 := by decide +kernel

theorem calc11_set_2288_eq : calc11_card_2243.envelope ∩ calc11_set_2287 = calc11_set_2288 := by decide +kernel

theorem calc11_set_2289_eq : calc11_card_2242.envelope ∩ calc11_set_2288 = calc11_set_2289 := by decide +kernel

theorem calc11_set_2290_eq : calc11_card_2241.envelope ∩ calc11_set_2289 = calc11_set_2290 := by decide +kernel

theorem calc11_set_2291_eq : calc11_card_2240.envelope ∩ calc11_set_2290 = calc11_set_2291 := by decide +kernel

theorem calc11_set_2292_eq : calc11_card_2239.envelope ∩ calc11_set_2291 = calc11_set_2292 := by decide +kernel

theorem calc11_set_2293_eq : calc11_card_2238.envelope ∩ calc11_set_2292 = calc11_set_2293 := by decide +kernel

theorem calc11_set_2294_eq : calc11_card_2237.envelope ∩ calc11_set_2293 = calc11_set_2294 := by decide +kernel

theorem calc11_set_2295_eq : calc11_card_2236.envelope ∩ calc11_set_2294 = calc11_set_2295 := by decide +kernel

theorem calc11_set_2296_eq : calc11_card_2235.envelope ∩ calc11_set_2295 = calc11_set_2296 := by decide +kernel

theorem calc11_set_2297_eq : calc11_set_2280 ∪ calc11_set_2296 = calc11_set_2297 := by decide +kernel

theorem calc11_finishA_2298 : calc11_set_2297.erase (8, 7) = card_726.required := by decide +kernel

theorem calc11_finishT_2298 : insert (8, 7) calc11_set_2281 = card_726.envelope := by decide +kernel

theorem eq_card_726 : card_726 = combine (8, 7) [placed 1 (3, 6) card_459, placed 2 (6, 11) card_579, placed 1 (3, 3) card_581, placed 1 (4, 4) card_654, placed 3 (12, 3) card_661, placed 5 (3, 10) card_677, placed 2 (4, 12) card_682, placed 1 (2, 2) card_694, placed 3 (13, 2) card_696, placed 5 (3, 11) card_698, placed 3 (13, 2) card_709, placed 3 (12, 4) card_710, placed 0 (3, 2) card_715, placed 2 (3, 13) card_717, placed 3 (13, 2) card_718, placed 3 (15, 2) card_724] := by
  rw [calc11_card_2234_eq, calc11_card_2235_eq, calc11_card_2236_eq, calc11_card_2237_eq, calc11_card_2238_eq, calc11_card_2239_eq, calc11_card_2240_eq, calc11_card_2241_eq, calc11_card_2242_eq, calc11_card_2243_eq, calc11_card_2244_eq, calc11_card_2245_eq, calc11_card_2246_eq, calc11_card_2247_eq, calc11_card_2248_eq, calc11_card_2249_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2250_eq, calc11_set_2252_eq, calc11_set_2254_eq, calc11_set_2256_eq, calc11_set_2258_eq, calc11_set_2260_eq, calc11_set_2262_eq, calc11_set_2264_eq, calc11_set_2266_eq, calc11_set_2268_eq, calc11_set_2270_eq, calc11_set_2272_eq, calc11_set_2274_eq, calc11_set_2276_eq, calc11_set_2278_eq, calc11_set_2280_eq, calc11_set_2282_eq, calc11_set_2283_eq, calc11_set_2284_eq, calc11_set_2285_eq, calc11_set_2286_eq, calc11_set_2287_eq, calc11_set_2288_eq, calc11_set_2289_eq, calc11_set_2290_eq, calc11_set_2291_eq, calc11_set_2292_eq, calc11_set_2293_eq, calc11_set_2294_eq, calc11_set_2295_eq, calc11_set_2296_eq, calc11_set_2297_eq, calc11_finishA_2298]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2251_eq, calc11_set_2253_eq, calc11_set_2255_eq, calc11_set_2257_eq, calc11_set_2259_eq, calc11_set_2261_eq, calc11_set_2263_eq, calc11_set_2265_eq, calc11_set_2267_eq, calc11_set_2269_eq, calc11_set_2271_eq, calc11_set_2273_eq, calc11_set_2275_eq, calc11_set_2277_eq, calc11_set_2279_eq, calc11_set_2281_eq, calc11_finishT_2298]
  · decide +kernel

theorem valid_726 : Valid card_726 := by
  rw [eq_card_726]
  apply combination_rule (8, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 6) valid_459
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 11) valid_579
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_581
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_654
  rcases hc with rfl | hc
  · exact placed_valid 3 (12, 3) valid_661
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 10) valid_677
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 12) valid_682
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_694
  rcases hc with rfl | hc
  · exact placed_valid 3 (13, 2) valid_696
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 11) valid_698
  rcases hc with rfl | hc
  · exact placed_valid 3 (13, 2) valid_709
  rcases hc with rfl | hc
  · exact placed_valid 3 (12, 4) valid_710
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_715
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 13) valid_717
  rcases hc with rfl | hc
  · exact placed_valid 3 (13, 2) valid_718
  subst c
  exact placed_valid 3 (15, 2) valid_724

theorem calc11_card_2299_eq : placed 0 (4, 3) card_648 = calc11_card_2299 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2300_eq : placed 1 (3, 4) card_648 = calc11_card_2300 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2301_eq : placed 5 (3, 12) card_648 = calc11_card_2301 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2302_eq : placed 2 (4, 13) card_648 = calc11_card_2302 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2303_eq : placed 1 (0, 0) card_708 = calc11_card_2303 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2304_eq : placed 4 (16, 0) card_708 = calc11_card_2304 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2305_eq : placed 2 (0, 16) card_708 = calc11_card_2305 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2306_eq : placed 7 (16, 16) card_708 = calc11_card_2306 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2307_eq : placed 0 (3, 3) card_712 = calc11_card_2307 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2308_eq : placed 1 (3, 3) card_712 = calc11_card_2308 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2309_eq : placed 4 (13, 3) card_712 = calc11_card_2309 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2310_eq : placed 5 (3, 13) card_712 = calc11_card_2310 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2311_eq : placed 2 (3, 13) card_712 = calc11_card_2311 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2312_eq : placed 3 (13, 3) card_712 = calc11_card_2312 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2313_eq : placed 6 (13, 13) card_712 = calc11_card_2313 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2314_eq : placed 7 (13, 13) card_712 = calc11_card_2314 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2315_eq : placed 4 (13, 3) card_713 = calc11_card_2315 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2316_eq : placed 5 (3, 13) card_713 = calc11_card_2316 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2317_eq : placed 2 (3, 13) card_713 = calc11_card_2317 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2318_eq : placed 3 (13, 3) card_713 = calc11_card_2318 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2319_eq : placed 0 (1, 1) card_725 = calc11_card_2319 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2320_eq : placed 1 (1, 1) card_725 = calc11_card_2320 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2321_eq : placed 4 (15, 1) card_725 = calc11_card_2321 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2322_eq : placed 5 (1, 15) card_725 = calc11_card_2322 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2323_eq : placed 2 (1, 15) card_725 = calc11_card_2323 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2324_eq : placed 3 (15, 1) card_725 = calc11_card_2324 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2325_eq : placed 6 (15, 15) card_725 = calc11_card_2325 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2326_eq : placed 7 (15, 15) card_725 = calc11_card_2326 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2327_eq : placed 1 (1, 1) card_726 = calc11_card_2327 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2328_eq : placed 4 (15, 1) card_726 = calc11_card_2328 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2329_eq : placed 2 (1, 15) card_726 = calc11_card_2329 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2330_eq : placed 6 (15, 15) card_726 = calc11_card_2330 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2331_eq : calc11_card_2330.required ∪ ∅ = calc11_set_2331 := by decide +kernel

theorem calc11_set_2332_eq : calc11_card_2330.envelope ∪ ∅ = calc11_set_2332 := by decide +kernel

theorem calc11_set_2333_eq : calc11_card_2329.required ∪ calc11_set_2331 = calc11_set_2333 := by decide +kernel

theorem calc11_set_2334_eq : calc11_card_2329.envelope ∪ calc11_set_2332 = calc11_set_2334 := by decide +kernel

theorem calc11_set_2335_eq : calc11_card_2328.required ∪ calc11_set_2333 = calc11_set_2335 := by decide +kernel

theorem calc11_set_2336_eq : calc11_card_2328.envelope ∪ calc11_set_2334 = calc11_set_2336 := by decide +kernel

theorem calc11_set_2337_eq : calc11_card_2327.required ∪ calc11_set_2335 = calc11_set_2337 := by decide +kernel

theorem calc11_set_2338_eq : calc11_card_2327.envelope ∪ calc11_set_2336 = calc11_set_2338 := by decide +kernel

theorem calc11_set_2339_eq : calc11_card_2326.required ∪ calc11_set_2337 = calc11_set_2339 := by decide +kernel

theorem calc11_set_2340_eq : calc11_card_2326.envelope ∪ calc11_set_2338 = calc11_set_2340 := by decide +kernel

theorem calc11_set_2341_eq : calc11_card_2325.required ∪ calc11_set_2339 = calc11_set_2341 := by decide +kernel

theorem calc11_set_2342_eq : calc11_card_2325.envelope ∪ calc11_set_2340 = calc11_set_2342 := by decide +kernel

theorem calc11_set_2343_eq : calc11_card_2324.required ∪ calc11_set_2341 = calc11_set_2343 := by decide +kernel

theorem calc11_set_2344_eq : calc11_card_2324.envelope ∪ calc11_set_2342 = calc11_set_2344 := by decide +kernel

theorem calc11_set_2345_eq : calc11_card_2323.required ∪ calc11_set_2343 = calc11_set_2345 := by decide +kernel

theorem calc11_set_2346_eq : calc11_card_2323.envelope ∪ calc11_set_2344 = calc11_set_2346 := by decide +kernel

theorem calc11_set_2347_eq : calc11_card_2322.required ∪ calc11_set_2345 = calc11_set_2347 := by decide +kernel

theorem calc11_set_2348_eq : calc11_card_2322.envelope ∪ calc11_set_2346 = calc11_set_2348 := by decide +kernel

theorem calc11_set_2349_eq : calc11_card_2321.required ∪ calc11_set_2347 = calc11_set_2349 := by decide +kernel

theorem calc11_set_2350_eq : calc11_card_2321.envelope ∪ calc11_set_2348 = calc11_set_2350 := by decide +kernel

theorem calc11_set_2351_eq : calc11_card_2320.required ∪ calc11_set_2349 = calc11_set_2351 := by decide +kernel

theorem calc11_set_2352_eq : calc11_card_2320.envelope ∪ calc11_set_2350 = calc11_set_2352 := by decide +kernel

theorem calc11_set_2353_eq : calc11_card_2319.required ∪ calc11_set_2351 = calc11_set_2353 := by decide +kernel

theorem calc11_set_2354_eq : calc11_card_2319.envelope ∪ calc11_set_2352 = calc11_set_2354 := by decide +kernel

theorem calc11_set_2355_eq : calc11_card_2318.required ∪ calc11_set_2353 = calc11_set_2355 := by decide +kernel

theorem calc11_set_2356_eq : calc11_card_2318.envelope ∪ calc11_set_2354 = calc11_set_2356 := by decide +kernel

theorem calc11_set_2357_eq : calc11_card_2317.required ∪ calc11_set_2355 = calc11_set_2357 := by decide +kernel

theorem calc11_set_2358_eq : calc11_card_2317.envelope ∪ calc11_set_2356 = calc11_set_2358 := by decide +kernel

theorem calc11_set_2359_eq : calc11_card_2316.required ∪ calc11_set_2357 = calc11_set_2359 := by decide +kernel

theorem calc11_set_2360_eq : calc11_card_2316.envelope ∪ calc11_set_2358 = calc11_set_2360 := by decide +kernel

theorem calc11_set_2361_eq : calc11_card_2315.required ∪ calc11_set_2359 = calc11_set_2361 := by decide +kernel

theorem calc11_set_2362_eq : calc11_card_2315.envelope ∪ calc11_set_2360 = calc11_set_2362 := by decide +kernel

theorem calc11_set_2363_eq : calc11_card_2314.required ∪ calc11_set_2361 = calc11_set_2363 := by decide +kernel

theorem calc11_set_2364_eq : calc11_card_2314.envelope ∪ calc11_set_2362 = calc11_set_2364 := by decide +kernel

theorem calc11_set_2365_eq : calc11_card_2313.required ∪ calc11_set_2363 = calc11_set_2365 := by decide +kernel

theorem calc11_set_2366_eq : calc11_card_2313.envelope ∪ calc11_set_2364 = calc11_set_2366 := by decide +kernel

theorem calc11_set_2367_eq : calc11_card_2312.required ∪ calc11_set_2365 = calc11_set_2367 := by decide +kernel

theorem calc11_set_2368_eq : calc11_card_2312.envelope ∪ calc11_set_2366 = calc11_set_2368 := by decide +kernel

theorem calc11_set_2369_eq : calc11_card_2311.required ∪ calc11_set_2367 = calc11_set_2369 := by decide +kernel

theorem calc11_set_2370_eq : calc11_card_2311.envelope ∪ calc11_set_2368 = calc11_set_2370 := by decide +kernel

theorem calc11_set_2371_eq : calc11_card_2310.required ∪ calc11_set_2369 = calc11_set_2371 := by decide +kernel

theorem calc11_set_2372_eq : calc11_card_2310.envelope ∪ calc11_set_2370 = calc11_set_2372 := by decide +kernel

theorem calc11_set_2373_eq : calc11_card_2309.required ∪ calc11_set_2371 = calc11_set_2373 := by decide +kernel

theorem calc11_set_2374_eq : calc11_card_2309.envelope ∪ calc11_set_2372 = calc11_set_2374 := by decide +kernel

theorem calc11_set_2375_eq : calc11_card_2308.required ∪ calc11_set_2373 = calc11_set_2375 := by decide +kernel

theorem calc11_set_2376_eq : calc11_card_2308.envelope ∪ calc11_set_2374 = calc11_set_2376 := by decide +kernel

theorem calc11_set_2377_eq : calc11_card_2307.required ∪ calc11_set_2375 = calc11_set_2377 := by decide +kernel

theorem calc11_set_2378_eq : calc11_card_2307.envelope ∪ calc11_set_2376 = calc11_set_2378 := by decide +kernel

theorem calc11_set_2379_eq : calc11_card_2306.required ∪ calc11_set_2377 = calc11_set_2379 := by decide +kernel

theorem calc11_set_2380_eq : calc11_card_2306.envelope ∪ calc11_set_2378 = calc11_set_2380 := by decide +kernel

theorem calc11_set_2381_eq : calc11_card_2305.required ∪ calc11_set_2379 = calc11_set_2381 := by decide +kernel

theorem calc11_set_2382_eq : calc11_card_2305.envelope ∪ calc11_set_2380 = calc11_set_2382 := by decide +kernel

theorem calc11_set_2383_eq : calc11_card_2304.required ∪ calc11_set_2381 = calc11_set_2383 := by decide +kernel

theorem calc11_set_2384_eq : calc11_card_2304.envelope ∪ calc11_set_2382 = calc11_set_2384 := by decide +kernel

theorem calc11_set_2385_eq : calc11_card_2303.required ∪ calc11_set_2383 = calc11_set_2385 := by decide +kernel

theorem calc11_set_2386_eq : calc11_card_2303.envelope ∪ calc11_set_2384 = calc11_set_2386 := by decide +kernel

theorem calc11_set_2387_eq : calc11_card_2302.required ∪ calc11_set_2385 = calc11_set_2387 := by decide +kernel

theorem calc11_set_2388_eq : calc11_card_2302.envelope ∪ calc11_set_2386 = calc11_set_2388 := by decide +kernel

theorem calc11_set_2389_eq : calc11_card_2301.required ∪ calc11_set_2387 = calc11_set_2389 := by decide +kernel

theorem calc11_set_2390_eq : calc11_card_2301.envelope ∪ calc11_set_2388 = calc11_set_2390 := by decide +kernel

theorem calc11_set_2391_eq : calc11_card_2300.required ∪ calc11_set_2389 = calc11_set_2391 := by decide +kernel

theorem calc11_set_2392_eq : calc11_card_2300.envelope ∪ calc11_set_2390 = calc11_set_2392 := by decide +kernel

theorem calc11_set_2393_eq : calc11_card_2299.required ∪ calc11_set_2391 = calc11_set_2393 := by decide +kernel

theorem calc11_set_2394_eq : calc11_card_2299.envelope ∪ calc11_set_2392 = calc11_set_2394 := by decide +kernel

theorem calc11_set_2395_eq : calc11_card_2330.envelope ∩ calc11_card_2299.envelope = calc11_set_2395 := by decide +kernel

theorem calc11_set_2396_eq : calc11_card_2329.envelope ∩ calc11_set_2395 = calc11_set_2396 := by decide +kernel

theorem calc11_set_2397_eq : calc11_card_2328.envelope ∩ calc11_set_2396 = calc11_set_2397 := by decide +kernel

theorem calc11_set_2398_eq : calc11_card_2327.envelope ∩ calc11_set_2397 = calc11_set_2398 := by decide +kernel

theorem calc11_set_2399_eq : calc11_card_2326.envelope ∩ calc11_set_2398 = calc11_set_2399 := by decide +kernel

theorem calc11_set_2400_eq : calc11_card_2325.envelope ∩ calc11_set_2399 = calc11_set_2400 := by decide +kernel

theorem calc11_set_2401_eq : calc11_card_2324.envelope ∩ calc11_set_2400 = calc11_set_2401 := by decide +kernel

theorem calc11_set_2402_eq : calc11_card_2323.envelope ∩ calc11_set_2401 = calc11_set_2402 := by decide +kernel

theorem calc11_set_2403_eq : calc11_card_2322.envelope ∩ calc11_set_2402 = calc11_set_2403 := by decide +kernel

theorem calc11_set_2404_eq : calc11_card_2321.envelope ∩ calc11_set_2403 = calc11_set_2404 := by decide +kernel

theorem calc11_set_2405_eq : calc11_card_2320.envelope ∩ calc11_set_2404 = calc11_set_2405 := by decide +kernel

theorem calc11_set_2406_eq : calc11_card_2319.envelope ∩ calc11_set_2405 = calc11_set_2406 := by decide +kernel

theorem calc11_set_2407_eq : calc11_card_2318.envelope ∩ calc11_set_2406 = calc11_set_2407 := by decide +kernel

theorem calc11_set_2408_eq : calc11_card_2317.envelope ∩ calc11_set_2407 = calc11_set_2408 := by decide +kernel

theorem calc11_set_2409_eq : calc11_card_2316.envelope ∩ calc11_set_2408 = calc11_set_2409 := by decide +kernel

theorem calc11_set_2410_eq : calc11_card_2315.envelope ∩ calc11_set_2409 = calc11_set_2410 := by decide +kernel

theorem calc11_set_2411_eq : calc11_card_2314.envelope ∩ calc11_set_2410 = calc11_set_2411 := by decide +kernel

theorem calc11_set_2412_eq : calc11_card_2313.envelope ∩ calc11_set_2411 = calc11_set_2412 := by decide +kernel

theorem calc11_set_2413_eq : calc11_card_2312.envelope ∩ calc11_set_2412 = calc11_set_2413 := by decide +kernel

theorem calc11_set_2414_eq : calc11_card_2311.envelope ∩ calc11_set_2413 = calc11_set_2414 := by decide +kernel

theorem calc11_set_2415_eq : calc11_card_2310.envelope ∩ calc11_set_2414 = calc11_set_2415 := by decide +kernel

theorem calc11_set_2416_eq : calc11_card_2309.envelope ∩ calc11_set_2415 = calc11_set_2416 := by decide +kernel

theorem calc11_set_2417_eq : calc11_card_2308.envelope ∩ calc11_set_2416 = calc11_set_2417 := by decide +kernel

theorem calc11_set_2418_eq : calc11_card_2307.envelope ∩ calc11_set_2417 = calc11_set_2418 := by decide +kernel

theorem calc11_set_2419_eq : calc11_card_2306.envelope ∩ calc11_set_2418 = calc11_set_2419 := by decide +kernel

theorem calc11_set_2420_eq : calc11_card_2305.envelope ∩ calc11_set_2419 = calc11_set_2420 := by decide +kernel

theorem calc11_set_2421_eq : calc11_card_2304.envelope ∩ calc11_set_2420 = calc11_set_2421 := by decide +kernel

theorem calc11_set_2422_eq : calc11_card_2303.envelope ∩ calc11_set_2421 = calc11_set_2422 := by decide +kernel

theorem calc11_set_2423_eq : calc11_card_2302.envelope ∩ calc11_set_2422 = calc11_set_2423 := by decide +kernel

theorem calc11_set_2424_eq : calc11_card_2301.envelope ∩ calc11_set_2423 = calc11_set_2424 := by decide +kernel

theorem calc11_set_2425_eq : calc11_card_2300.envelope ∩ calc11_set_2424 = calc11_set_2425 := by decide +kernel

theorem calc11_set_2426_eq : calc11_set_2393 ∪ calc11_set_2425 = calc11_set_2426 := by decide +kernel

theorem calc11_finishA_2427 : calc11_set_2426.erase (8, 8) = card_727.required := by decide +kernel

theorem calc11_finishT_2427 : insert (8, 8) calc11_set_2394 = card_727.envelope := by decide +kernel

theorem eq_card_727 : card_727 = combine (8, 8) [placed 0 (4, 3) card_648, placed 1 (3, 4) card_648, placed 5 (3, 12) card_648, placed 2 (4, 13) card_648, placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] := by
  have hL_32 : ([] : List Card) = [] := rfl
  have hL_31 : [placed 6 (15, 15) card_726] = [calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2330_eq hL_32
  have hL_30 : [placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2329_eq hL_31
  have hL_29 : [placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2328_eq hL_30
  have hL_28 : [placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2327_eq hL_29
  have hL_27 : [placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2326_eq hL_28
  have hL_26 : [placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2325_eq hL_27
  have hL_25 : [placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2324_eq hL_26
  have hL_24 : [placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2323_eq hL_25
  have hL_23 : [placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2322_eq hL_24
  have hL_22 : [placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2321_eq hL_23
  have hL_21 : [placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2320_eq hL_22
  have hL_20 : [placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2319_eq hL_21
  have hL_19 : [placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2318_eq hL_20
  have hL_18 : [placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2317_eq hL_19
  have hL_17 : [placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2316_eq hL_18
  have hL_16 : [placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2315_eq hL_17
  have hL_15 : [placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2314_eq hL_16
  have hL_14 : [placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2313_eq hL_15
  have hL_13 : [placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2312_eq hL_14
  have hL_12 : [placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2311_eq hL_13
  have hL_11 : [placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2310_eq hL_12
  have hL_10 : [placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2309_eq hL_11
  have hL_9 : [placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2308_eq hL_10
  have hL_8 : [placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2307_eq hL_9
  have hL_7 : [placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2306_eq hL_8
  have hL_6 : [placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2305_eq hL_7
  have hL_5 : [placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2304_eq hL_6
  have hL_4 : [placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2303_eq hL_5
  have hL_3 : [placed 2 (4, 13) card_648, placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2302_eq hL_4
  have hL_2 : [placed 5 (3, 12) card_648, placed 2 (4, 13) card_648, placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2301_eq hL_3
  have hL_1 : [placed 1 (3, 4) card_648, placed 5 (3, 12) card_648, placed 2 (4, 13) card_648, placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2300_eq hL_2
  have hL_0 : [placed 0 (4, 3) card_648, placed 1 (3, 4) card_648, placed 5 (3, 12) card_648, placed 2 (4, 13) card_648, placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2299, calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2299_eq hL_1
  have hA_31 : unionRequired [calc11_card_2330] = calc11_set_2331 :=
    calc11_set_2331_eq
  have hA_30 : unionRequired [calc11_card_2329, calc11_card_2330] = calc11_set_2333 :=
    (congrArg (fun s : Finset Cell => calc11_card_2329.required ∪ s) hA_31).trans calc11_set_2333_eq
  have hA_29 : unionRequired [calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2335 :=
    (congrArg (fun s : Finset Cell => calc11_card_2328.required ∪ s) hA_30).trans calc11_set_2335_eq
  have hA_28 : unionRequired [calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2337 :=
    (congrArg (fun s : Finset Cell => calc11_card_2327.required ∪ s) hA_29).trans calc11_set_2337_eq
  have hA_27 : unionRequired [calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2339 :=
    (congrArg (fun s : Finset Cell => calc11_card_2326.required ∪ s) hA_28).trans calc11_set_2339_eq
  have hA_26 : unionRequired [calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2341 :=
    (congrArg (fun s : Finset Cell => calc11_card_2325.required ∪ s) hA_27).trans calc11_set_2341_eq
  have hA_25 : unionRequired [calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2343 :=
    (congrArg (fun s : Finset Cell => calc11_card_2324.required ∪ s) hA_26).trans calc11_set_2343_eq
  have hA_24 : unionRequired [calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2345 :=
    (congrArg (fun s : Finset Cell => calc11_card_2323.required ∪ s) hA_25).trans calc11_set_2345_eq
  have hA_23 : unionRequired [calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2347 :=
    (congrArg (fun s : Finset Cell => calc11_card_2322.required ∪ s) hA_24).trans calc11_set_2347_eq
  have hA_22 : unionRequired [calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2349 :=
    (congrArg (fun s : Finset Cell => calc11_card_2321.required ∪ s) hA_23).trans calc11_set_2349_eq
  have hA_21 : unionRequired [calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2351 :=
    (congrArg (fun s : Finset Cell => calc11_card_2320.required ∪ s) hA_22).trans calc11_set_2351_eq
  have hA_20 : unionRequired [calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2353 :=
    (congrArg (fun s : Finset Cell => calc11_card_2319.required ∪ s) hA_21).trans calc11_set_2353_eq
  have hA_19 : unionRequired [calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2355 :=
    (congrArg (fun s : Finset Cell => calc11_card_2318.required ∪ s) hA_20).trans calc11_set_2355_eq
  have hA_18 : unionRequired [calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2357 :=
    (congrArg (fun s : Finset Cell => calc11_card_2317.required ∪ s) hA_19).trans calc11_set_2357_eq
  have hA_17 : unionRequired [calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2359 :=
    (congrArg (fun s : Finset Cell => calc11_card_2316.required ∪ s) hA_18).trans calc11_set_2359_eq
  have hA_16 : unionRequired [calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2361 :=
    (congrArg (fun s : Finset Cell => calc11_card_2315.required ∪ s) hA_17).trans calc11_set_2361_eq
  have hA_15 : unionRequired [calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2363 :=
    (congrArg (fun s : Finset Cell => calc11_card_2314.required ∪ s) hA_16).trans calc11_set_2363_eq
  have hA_14 : unionRequired [calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2365 :=
    (congrArg (fun s : Finset Cell => calc11_card_2313.required ∪ s) hA_15).trans calc11_set_2365_eq
  have hA_13 : unionRequired [calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2367 :=
    (congrArg (fun s : Finset Cell => calc11_card_2312.required ∪ s) hA_14).trans calc11_set_2367_eq
  have hA_12 : unionRequired [calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2369 :=
    (congrArg (fun s : Finset Cell => calc11_card_2311.required ∪ s) hA_13).trans calc11_set_2369_eq
  have hA_11 : unionRequired [calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2371 :=
    (congrArg (fun s : Finset Cell => calc11_card_2310.required ∪ s) hA_12).trans calc11_set_2371_eq
  have hA_10 : unionRequired [calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2373 :=
    (congrArg (fun s : Finset Cell => calc11_card_2309.required ∪ s) hA_11).trans calc11_set_2373_eq
  have hA_9 : unionRequired [calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2375 :=
    (congrArg (fun s : Finset Cell => calc11_card_2308.required ∪ s) hA_10).trans calc11_set_2375_eq
  have hA_8 : unionRequired [calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2377 :=
    (congrArg (fun s : Finset Cell => calc11_card_2307.required ∪ s) hA_9).trans calc11_set_2377_eq
  have hA_7 : unionRequired [calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2379 :=
    (congrArg (fun s : Finset Cell => calc11_card_2306.required ∪ s) hA_8).trans calc11_set_2379_eq
  have hA_6 : unionRequired [calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2381 :=
    (congrArg (fun s : Finset Cell => calc11_card_2305.required ∪ s) hA_7).trans calc11_set_2381_eq
  have hA_5 : unionRequired [calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2383 :=
    (congrArg (fun s : Finset Cell => calc11_card_2304.required ∪ s) hA_6).trans calc11_set_2383_eq
  have hA_4 : unionRequired [calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2385 :=
    (congrArg (fun s : Finset Cell => calc11_card_2303.required ∪ s) hA_5).trans calc11_set_2385_eq
  have hA_3 : unionRequired [calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2387 :=
    (congrArg (fun s : Finset Cell => calc11_card_2302.required ∪ s) hA_4).trans calc11_set_2387_eq
  have hA_2 : unionRequired [calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2389 :=
    (congrArg (fun s : Finset Cell => calc11_card_2301.required ∪ s) hA_3).trans calc11_set_2389_eq
  have hA_1 : unionRequired [calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2391 :=
    (congrArg (fun s : Finset Cell => calc11_card_2300.required ∪ s) hA_2).trans calc11_set_2391_eq
  have hA_0 : unionRequired [calc11_card_2299, calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2393 :=
    (congrArg (fun s : Finset Cell => calc11_card_2299.required ∪ s) hA_1).trans calc11_set_2393_eq
  have hT_31 : unionEnvelope [calc11_card_2330] = calc11_set_2332 :=
    calc11_set_2332_eq
  have hT_30 : unionEnvelope [calc11_card_2329, calc11_card_2330] = calc11_set_2334 :=
    (congrArg (fun s : Finset Cell => calc11_card_2329.envelope ∪ s) hT_31).trans calc11_set_2334_eq
  have hT_29 : unionEnvelope [calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2336 :=
    (congrArg (fun s : Finset Cell => calc11_card_2328.envelope ∪ s) hT_30).trans calc11_set_2336_eq
  have hT_28 : unionEnvelope [calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2338 :=
    (congrArg (fun s : Finset Cell => calc11_card_2327.envelope ∪ s) hT_29).trans calc11_set_2338_eq
  have hT_27 : unionEnvelope [calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2340 :=
    (congrArg (fun s : Finset Cell => calc11_card_2326.envelope ∪ s) hT_28).trans calc11_set_2340_eq
  have hT_26 : unionEnvelope [calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2342 :=
    (congrArg (fun s : Finset Cell => calc11_card_2325.envelope ∪ s) hT_27).trans calc11_set_2342_eq
  have hT_25 : unionEnvelope [calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2344 :=
    (congrArg (fun s : Finset Cell => calc11_card_2324.envelope ∪ s) hT_26).trans calc11_set_2344_eq
  have hT_24 : unionEnvelope [calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2346 :=
    (congrArg (fun s : Finset Cell => calc11_card_2323.envelope ∪ s) hT_25).trans calc11_set_2346_eq
  have hT_23 : unionEnvelope [calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2348 :=
    (congrArg (fun s : Finset Cell => calc11_card_2322.envelope ∪ s) hT_24).trans calc11_set_2348_eq
  have hT_22 : unionEnvelope [calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2350 :=
    (congrArg (fun s : Finset Cell => calc11_card_2321.envelope ∪ s) hT_23).trans calc11_set_2350_eq
  have hT_21 : unionEnvelope [calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2352 :=
    (congrArg (fun s : Finset Cell => calc11_card_2320.envelope ∪ s) hT_22).trans calc11_set_2352_eq
  have hT_20 : unionEnvelope [calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2354 :=
    (congrArg (fun s : Finset Cell => calc11_card_2319.envelope ∪ s) hT_21).trans calc11_set_2354_eq
  have hT_19 : unionEnvelope [calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2356 :=
    (congrArg (fun s : Finset Cell => calc11_card_2318.envelope ∪ s) hT_20).trans calc11_set_2356_eq
  have hT_18 : unionEnvelope [calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2358 :=
    (congrArg (fun s : Finset Cell => calc11_card_2317.envelope ∪ s) hT_19).trans calc11_set_2358_eq
  have hT_17 : unionEnvelope [calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2360 :=
    (congrArg (fun s : Finset Cell => calc11_card_2316.envelope ∪ s) hT_18).trans calc11_set_2360_eq
  have hT_16 : unionEnvelope [calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2362 :=
    (congrArg (fun s : Finset Cell => calc11_card_2315.envelope ∪ s) hT_17).trans calc11_set_2362_eq
  have hT_15 : unionEnvelope [calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2364 :=
    (congrArg (fun s : Finset Cell => calc11_card_2314.envelope ∪ s) hT_16).trans calc11_set_2364_eq
  have hT_14 : unionEnvelope [calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2366 :=
    (congrArg (fun s : Finset Cell => calc11_card_2313.envelope ∪ s) hT_15).trans calc11_set_2366_eq
  have hT_13 : unionEnvelope [calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2368 :=
    (congrArg (fun s : Finset Cell => calc11_card_2312.envelope ∪ s) hT_14).trans calc11_set_2368_eq
  have hT_12 : unionEnvelope [calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2370 :=
    (congrArg (fun s : Finset Cell => calc11_card_2311.envelope ∪ s) hT_13).trans calc11_set_2370_eq
  have hT_11 : unionEnvelope [calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2372 :=
    (congrArg (fun s : Finset Cell => calc11_card_2310.envelope ∪ s) hT_12).trans calc11_set_2372_eq
  have hT_10 : unionEnvelope [calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2374 :=
    (congrArg (fun s : Finset Cell => calc11_card_2309.envelope ∪ s) hT_11).trans calc11_set_2374_eq
  have hT_9 : unionEnvelope [calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2376 :=
    (congrArg (fun s : Finset Cell => calc11_card_2308.envelope ∪ s) hT_10).trans calc11_set_2376_eq
  have hT_8 : unionEnvelope [calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2378 :=
    (congrArg (fun s : Finset Cell => calc11_card_2307.envelope ∪ s) hT_9).trans calc11_set_2378_eq
  have hT_7 : unionEnvelope [calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2380 :=
    (congrArg (fun s : Finset Cell => calc11_card_2306.envelope ∪ s) hT_8).trans calc11_set_2380_eq
  have hT_6 : unionEnvelope [calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2382 :=
    (congrArg (fun s : Finset Cell => calc11_card_2305.envelope ∪ s) hT_7).trans calc11_set_2382_eq
  have hT_5 : unionEnvelope [calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2384 :=
    (congrArg (fun s : Finset Cell => calc11_card_2304.envelope ∪ s) hT_6).trans calc11_set_2384_eq
  have hT_4 : unionEnvelope [calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2386 :=
    (congrArg (fun s : Finset Cell => calc11_card_2303.envelope ∪ s) hT_5).trans calc11_set_2386_eq
  have hT_3 : unionEnvelope [calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2388 :=
    (congrArg (fun s : Finset Cell => calc11_card_2302.envelope ∪ s) hT_4).trans calc11_set_2388_eq
  have hT_2 : unionEnvelope [calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2390 :=
    (congrArg (fun s : Finset Cell => calc11_card_2301.envelope ∪ s) hT_3).trans calc11_set_2390_eq
  have hT_1 : unionEnvelope [calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2392 :=
    (congrArg (fun s : Finset Cell => calc11_card_2300.envelope ∪ s) hT_2).trans calc11_set_2392_eq
  have hT_0 : unionEnvelope [calc11_card_2299, calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2394 :=
    (congrArg (fun s : Finset Cell => calc11_card_2299.envelope ∪ s) hT_1).trans calc11_set_2394_eq
  have hI_31 : commonEnvelope [calc11_card_2299, calc11_card_2330] = calc11_set_2395 :=
    calc11_set_2395_eq
  have hI_30 : commonEnvelope [calc11_card_2299, calc11_card_2329, calc11_card_2330] = calc11_set_2396 :=
    (congrArg (fun s : Finset Cell => calc11_card_2329.envelope ∩ s) hI_31).trans calc11_set_2396_eq
  have hI_29 : commonEnvelope [calc11_card_2299, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2397 :=
    (congrArg (fun s : Finset Cell => calc11_card_2328.envelope ∩ s) hI_30).trans calc11_set_2397_eq
  have hI_28 : commonEnvelope [calc11_card_2299, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2398 :=
    (congrArg (fun s : Finset Cell => calc11_card_2327.envelope ∩ s) hI_29).trans calc11_set_2398_eq
  have hI_27 : commonEnvelope [calc11_card_2299, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2399 :=
    (congrArg (fun s : Finset Cell => calc11_card_2326.envelope ∩ s) hI_28).trans calc11_set_2399_eq
  have hI_26 : commonEnvelope [calc11_card_2299, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2400 :=
    (congrArg (fun s : Finset Cell => calc11_card_2325.envelope ∩ s) hI_27).trans calc11_set_2400_eq
  have hI_25 : commonEnvelope [calc11_card_2299, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2401 :=
    (congrArg (fun s : Finset Cell => calc11_card_2324.envelope ∩ s) hI_26).trans calc11_set_2401_eq
  have hI_24 : commonEnvelope [calc11_card_2299, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2402 :=
    (congrArg (fun s : Finset Cell => calc11_card_2323.envelope ∩ s) hI_25).trans calc11_set_2402_eq
  have hI_23 : commonEnvelope [calc11_card_2299, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2403 :=
    (congrArg (fun s : Finset Cell => calc11_card_2322.envelope ∩ s) hI_24).trans calc11_set_2403_eq
  have hI_22 : commonEnvelope [calc11_card_2299, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2404 :=
    (congrArg (fun s : Finset Cell => calc11_card_2321.envelope ∩ s) hI_23).trans calc11_set_2404_eq
  have hI_21 : commonEnvelope [calc11_card_2299, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2405 :=
    (congrArg (fun s : Finset Cell => calc11_card_2320.envelope ∩ s) hI_22).trans calc11_set_2405_eq
  have hI_20 : commonEnvelope [calc11_card_2299, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2406 :=
    (congrArg (fun s : Finset Cell => calc11_card_2319.envelope ∩ s) hI_21).trans calc11_set_2406_eq
  have hI_19 : commonEnvelope [calc11_card_2299, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2407 :=
    (congrArg (fun s : Finset Cell => calc11_card_2318.envelope ∩ s) hI_20).trans calc11_set_2407_eq
  have hI_18 : commonEnvelope [calc11_card_2299, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2408 :=
    (congrArg (fun s : Finset Cell => calc11_card_2317.envelope ∩ s) hI_19).trans calc11_set_2408_eq
  have hI_17 : commonEnvelope [calc11_card_2299, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2409 :=
    (congrArg (fun s : Finset Cell => calc11_card_2316.envelope ∩ s) hI_18).trans calc11_set_2409_eq
  have hI_16 : commonEnvelope [calc11_card_2299, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2410 :=
    (congrArg (fun s : Finset Cell => calc11_card_2315.envelope ∩ s) hI_17).trans calc11_set_2410_eq
  have hI_15 : commonEnvelope [calc11_card_2299, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2411 :=
    (congrArg (fun s : Finset Cell => calc11_card_2314.envelope ∩ s) hI_16).trans calc11_set_2411_eq
  have hI_14 : commonEnvelope [calc11_card_2299, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2412 :=
    (congrArg (fun s : Finset Cell => calc11_card_2313.envelope ∩ s) hI_15).trans calc11_set_2412_eq
  have hI_13 : commonEnvelope [calc11_card_2299, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2413 :=
    (congrArg (fun s : Finset Cell => calc11_card_2312.envelope ∩ s) hI_14).trans calc11_set_2413_eq
  have hI_12 : commonEnvelope [calc11_card_2299, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2414 :=
    (congrArg (fun s : Finset Cell => calc11_card_2311.envelope ∩ s) hI_13).trans calc11_set_2414_eq
  have hI_11 : commonEnvelope [calc11_card_2299, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2415 :=
    (congrArg (fun s : Finset Cell => calc11_card_2310.envelope ∩ s) hI_12).trans calc11_set_2415_eq
  have hI_10 : commonEnvelope [calc11_card_2299, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2416 :=
    (congrArg (fun s : Finset Cell => calc11_card_2309.envelope ∩ s) hI_11).trans calc11_set_2416_eq
  have hI_9 : commonEnvelope [calc11_card_2299, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2417 :=
    (congrArg (fun s : Finset Cell => calc11_card_2308.envelope ∩ s) hI_10).trans calc11_set_2417_eq
  have hI_8 : commonEnvelope [calc11_card_2299, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2418 :=
    (congrArg (fun s : Finset Cell => calc11_card_2307.envelope ∩ s) hI_9).trans calc11_set_2418_eq
  have hI_7 : commonEnvelope [calc11_card_2299, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2419 :=
    (congrArg (fun s : Finset Cell => calc11_card_2306.envelope ∩ s) hI_8).trans calc11_set_2419_eq
  have hI_6 : commonEnvelope [calc11_card_2299, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2420 :=
    (congrArg (fun s : Finset Cell => calc11_card_2305.envelope ∩ s) hI_7).trans calc11_set_2420_eq
  have hI_5 : commonEnvelope [calc11_card_2299, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2421 :=
    (congrArg (fun s : Finset Cell => calc11_card_2304.envelope ∩ s) hI_6).trans calc11_set_2421_eq
  have hI_4 : commonEnvelope [calc11_card_2299, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2422 :=
    (congrArg (fun s : Finset Cell => calc11_card_2303.envelope ∩ s) hI_5).trans calc11_set_2422_eq
  have hI_3 : commonEnvelope [calc11_card_2299, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2423 :=
    (congrArg (fun s : Finset Cell => calc11_card_2302.envelope ∩ s) hI_4).trans calc11_set_2423_eq
  have hI_2 : commonEnvelope [calc11_card_2299, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2424 :=
    (congrArg (fun s : Finset Cell => calc11_card_2301.envelope ∩ s) hI_3).trans calc11_set_2424_eq
  have hI_1 : commonEnvelope [calc11_card_2299, calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2425 :=
    (congrArg (fun s : Finset Cell => calc11_card_2300.envelope ∩ s) hI_2).trans calc11_set_2425_eq
  have hC : card_727 = combine (8, 8) [calc11_card_2299, calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] := by
    apply computed_card_ext
    · exact ((congrArg (fun s : Finset Cell => s.erase (8, 8))
        ((congrArg₂ (fun a b : Finset Cell => a ∪ b) hA_0 hI_1).trans calc11_set_2426_eq)).trans calc11_finishA_2427).symm
    · exact ((congrArg (fun s : Finset Cell => insert (8, 8) s) hT_0).trans calc11_finishT_2427).symm
    · decide +kernel
  exact hC.trans (congrArg (combine (8, 8)) hL_0).symm

theorem valid_727 : Valid card_727 := by
  rw [eq_card_727]
  apply combination_rule (8, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_648
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_648
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 12) valid_648
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 13) valid_648
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_708
  rcases hc with rfl | hc
  · exact placed_valid 4 (16, 0) valid_708
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 16) valid_708
  rcases hc with rfl | hc
  · exact placed_valid 7 (16, 16) valid_708
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 4 (13, 3) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 13) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 13) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 3 (13, 3) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 6 (13, 13) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 7 (13, 13) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 4 (13, 3) valid_713
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 13) valid_713
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 13) valid_713
  rcases hc with rfl | hc
  · exact placed_valid 3 (13, 3) valid_713
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 4 (15, 1) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 15) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 15) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 3 (15, 1) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 6 (15, 15) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 7 (15, 15) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_726
  rcases hc with rfl | hc
  · exact placed_valid 4 (15, 1) valid_726
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 15) valid_726
  subst c
  exact placed_valid 6 (15, 15) valid_726

theorem block11_valid : Valid card_704 ∧ Valid card_705 ∧ Valid card_706 ∧ Valid card_707 ∧ Valid card_708 ∧ Valid card_709 ∧ Valid card_710 ∧ Valid card_711 ∧ Valid card_712 ∧ Valid card_713 ∧ Valid card_714 ∧ Valid card_715 ∧ Valid card_716 ∧ Valid card_717 ∧ Valid card_718 ∧ Valid card_719 ∧ Valid card_720 ∧ Valid card_721 ∧ Valid card_722 ∧ Valid card_723 ∧ Valid card_724 ∧ Valid card_725 ∧ Valid card_726 ∧ Valid card_727 ∧ True :=
  ⟨valid_704, valid_705, valid_706, valid_707, valid_708, valid_709, valid_710, valid_711, valid_712, valid_713, valid_714, valid_715, valid_716, valid_717, valid_718, valid_719, valid_720, valid_721, valid_722, valid_723, valid_724, valid_725, valid_726, valid_727, True.intro⟩

end OAI.Snaky21.Certificate
