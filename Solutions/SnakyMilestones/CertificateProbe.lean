import Definitions.Def_SnakyCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate

theorem row_ext {c d : RowData} (hA : c.A = d.A)
    (hH : c.H = d.H) (hh : c.height = d.height) : c = d := by
  cases c; cases d; cases hA; cases hH; cases hh; rfl

def Good (d : RowData) : Prop :=
  d.A ⊆ d.H ∧ origin ∈ d.H ∧ origin ∉ d.A ∧ d.height ≤ 34

def EntryGood (i : ℕ) : Prop :=
  let e := entryAt i
  e.index = i ∧ e.terms ≠ [] ∧ ∀ t ∈ e.terms, t.child < i

theorem chunk_size_0 : tableChunk_0.size = 20 := by decide +kernel
theorem chunk_size_1 : tableChunk_1.size = 20 := by decide +kernel
theorem chunk_size_2 : tableChunk_2.size = 20 := by decide +kernel
theorem chunk_size_3 : tableChunk_3.size = 20 := by decide +kernel
theorem chunk_size_4 : tableChunk_4.size = 20 := by decide +kernel
theorem chunk_size_5 : tableChunk_5.size = 20 := by decide +kernel
theorem chunk_size_6 : tableChunk_6.size = 20 := by decide +kernel
theorem chunk_size_7 : tableChunk_7.size = 20 := by decide +kernel
theorem chunk_size_8 : tableChunk_8.size = 20 := by decide +kernel
theorem chunk_size_9 : tableChunk_9.size = 20 := by decide +kernel
theorem chunk_size_10 : tableChunk_10.size = 20 := by decide +kernel
theorem chunk_size_11 : tableChunk_11.size = 20 := by decide +kernel
theorem chunk_size_12 : tableChunk_12.size = 20 := by decide +kernel
theorem chunk_size_13 : tableChunk_13.size = 20 := by decide +kernel
theorem chunk_size_14 : tableChunk_14.size = 20 := by decide +kernel
theorem chunk_size_15 : tableChunk_15.size = 20 := by decide +kernel
theorem chunk_size_16 : tableChunk_16.size = 20 := by decide +kernel
theorem chunk_size_17 : tableChunk_17.size = 20 := by decide +kernel
theorem chunk_size_18 : tableChunk_18.size = 20 := by decide +kernel
theorem chunk_size_19 : tableChunk_19.size = 20 := by decide +kernel
theorem chunk_size_20 : tableChunk_20.size = 20 := by decide +kernel
theorem chunk_size_21 : tableChunk_21.size = 20 := by decide +kernel
theorem chunk_size_22 : tableChunk_22.size = 20 := by decide +kernel
theorem chunk_size_23 : tableChunk_23.size = 20 := by decide +kernel
theorem chunk_size_24 : tableChunk_24.size = 20 := by decide +kernel
theorem chunk_size_25 : tableChunk_25.size = 20 := by decide +kernel
theorem chunk_size_26 : tableChunk_26.size = 20 := by decide +kernel
theorem chunk_size_27 : tableChunk_27.size = 20 := by decide +kernel
theorem chunk_size_28 : tableChunk_28.size = 20 := by decide +kernel
theorem chunk_size_29 : tableChunk_29.size = 20 := by decide +kernel
theorem chunk_size_30 : tableChunk_30.size = 10 := by decide +kernel
theorem entry_chunk_0 (j : ℕ) (hj : j < 20) :
    entryAt (6 + j) = tableChunk_0[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 6 + j - 6 = 0 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 0 + j) (by
      have hn : 0 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 0 + j) (by
      have hn : 0 + j < 140 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := (tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)))
    (ys := ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) (i := 0 + j) (by
      have hn : 0 + j < 60 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := tableChunk_0)
    (ys := (tableChunk_1 ++ tableChunk_2)) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_1 (j : ℕ) (hj : j < 20) :
    entryAt (26 + j) = tableChunk_1[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 26 + j - 6 = 20 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 20 + j) (by
      have hn : 20 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 20 + j) (by
      have hn : 20 + j < 140 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := (tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)))
    (ys := ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) (i := 20 + j) (by
      have hn : 20 + j < 60 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := tableChunk_0)
    (ys := (tableChunk_1 ++ tableChunk_2)) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := tableChunk_1)
    (ys := tableChunk_2) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_2 (j : ℕ) (hj : j < 20) :
    entryAt (46 + j) = tableChunk_2[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 46 + j - 6 = 40 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 40 + j) (by
      have hn : 40 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 40 + j) (by
      have hn : 40 + j < 140 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := (tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)))
    (ys := ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) (i := 40 + j) (by
      have hn : 40 + j < 60 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := tableChunk_0)
    (ys := (tableChunk_1 ++ tableChunk_2)) (i := 40 + j) (by
      have hn : 20 ≤ 40 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 40 + j - 20 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := tableChunk_1)
    (ys := tableChunk_2) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_3 (j : ℕ) (hj : j < 20) :
    entryAt (66 + j) = tableChunk_3[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 66 + j - 6 = 60 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 60 + j) (by
      have hn : 60 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 60 + j) (by
      have hn : 60 + j < 140 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := (tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)))
    (ys := ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) (i := 60 + j) (by
      have hn : 60 ≤ 60 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 60 + j - 60 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (tableChunk_3 ++ tableChunk_4))
    (ys := (tableChunk_5 ++ tableChunk_6)) (i := 0 + j) (by
      have hn : 0 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := tableChunk_3)
    (ys := tableChunk_4) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_4 (j : ℕ) (hj : j < 20) :
    entryAt (86 + j) = tableChunk_4[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 86 + j - 6 = 80 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 80 + j) (by
      have hn : 80 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 80 + j) (by
      have hn : 80 + j < 140 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := (tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)))
    (ys := ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) (i := 80 + j) (by
      have hn : 60 ≤ 80 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 80 + j - 60 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (tableChunk_3 ++ tableChunk_4))
    (ys := (tableChunk_5 ++ tableChunk_6)) (i := 20 + j) (by
      have hn : 20 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := tableChunk_3)
    (ys := tableChunk_4) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_5 (j : ℕ) (hj : j < 20) :
    entryAt (106 + j) = tableChunk_5[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 106 + j - 6 = 100 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 100 + j) (by
      have hn : 100 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 100 + j) (by
      have hn : 100 + j < 140 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := (tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)))
    (ys := ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) (i := 100 + j) (by
      have hn : 60 ≤ 100 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 100 + j - 60 = 40 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (tableChunk_3 ++ tableChunk_4))
    (ys := (tableChunk_5 ++ tableChunk_6)) (i := 40 + j) (by
      have hn : 40 ≤ 40 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 40 + j - 40 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := tableChunk_5)
    (ys := tableChunk_6) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_6 (j : ℕ) (hj : j < 20) :
    entryAt (126 + j) = tableChunk_6[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 126 + j - 6 = 120 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 120 + j) (by
      have hn : 120 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 120 + j) (by
      have hn : 120 + j < 140 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := (tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)))
    (ys := ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) (i := 120 + j) (by
      have hn : 60 ≤ 120 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 120 + j - 60 = 60 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (tableChunk_3 ++ tableChunk_4))
    (ys := (tableChunk_5 ++ tableChunk_6)) (i := 60 + j) (by
      have hn : 40 ≤ 60 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 60 + j - 40 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := tableChunk_5)
    (ys := tableChunk_6) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_7 (j : ℕ) (hj : j < 20) :
    entryAt (146 + j) = tableChunk_7[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 146 + j - 6 = 140 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 140 + j) (by
      have hn : 140 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 140 + j) (by
      have hn : 140 ≤ 140 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 140 + j - 140 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := ((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)))
    (ys := ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14))) (i := 0 + j) (by
      have hn : 0 + j < 80 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := (tableChunk_7 ++ tableChunk_8))
    (ys := (tableChunk_9 ++ tableChunk_10)) (i := 0 + j) (by
      have hn : 0 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := tableChunk_7)
    (ys := tableChunk_8) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_8 (j : ℕ) (hj : j < 20) :
    entryAt (166 + j) = tableChunk_8[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 166 + j - 6 = 160 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 160 + j) (by
      have hn : 160 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 160 + j) (by
      have hn : 140 ≤ 160 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 160 + j - 140 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := ((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)))
    (ys := ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14))) (i := 20 + j) (by
      have hn : 20 + j < 80 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := (tableChunk_7 ++ tableChunk_8))
    (ys := (tableChunk_9 ++ tableChunk_10)) (i := 20 + j) (by
      have hn : 20 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := tableChunk_7)
    (ys := tableChunk_8) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_9 (j : ℕ) (hj : j < 20) :
    entryAt (186 + j) = tableChunk_9[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 186 + j - 6 = 180 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 180 + j) (by
      have hn : 180 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 180 + j) (by
      have hn : 140 ≤ 180 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 180 + j - 140 = 40 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := ((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)))
    (ys := ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14))) (i := 40 + j) (by
      have hn : 40 + j < 80 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := (tableChunk_7 ++ tableChunk_8))
    (ys := (tableChunk_9 ++ tableChunk_10)) (i := 40 + j) (by
      have hn : 40 ≤ 40 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 40 + j - 40 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := tableChunk_9)
    (ys := tableChunk_10) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_10 (j : ℕ) (hj : j < 20) :
    entryAt (206 + j) = tableChunk_10[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 206 + j - 6 = 200 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 200 + j) (by
      have hn : 200 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 200 + j) (by
      have hn : 140 ≤ 200 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 200 + j - 140 = 60 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := ((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)))
    (ys := ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14))) (i := 60 + j) (by
      have hn : 60 + j < 80 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := (tableChunk_7 ++ tableChunk_8))
    (ys := (tableChunk_9 ++ tableChunk_10)) (i := 60 + j) (by
      have hn : 40 ≤ 60 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 60 + j - 40 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := tableChunk_9)
    (ys := tableChunk_10) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_11 (j : ℕ) (hj : j < 20) :
    entryAt (226 + j) = tableChunk_11[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 226 + j - 6 = 220 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 220 + j) (by
      have hn : 220 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 220 + j) (by
      have hn : 140 ≤ 220 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 220 + j - 140 = 80 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := ((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)))
    (ys := ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14))) (i := 80 + j) (by
      have hn : 80 ≤ 80 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 80 + j - 80 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (tableChunk_11 ++ tableChunk_12))
    (ys := (tableChunk_13 ++ tableChunk_14)) (i := 0 + j) (by
      have hn : 0 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := tableChunk_11)
    (ys := tableChunk_12) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_12 (j : ℕ) (hj : j < 20) :
    entryAt (246 + j) = tableChunk_12[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 246 + j - 6 = 240 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 240 + j) (by
      have hn : 240 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 240 + j) (by
      have hn : 140 ≤ 240 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 240 + j - 140 = 100 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := ((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)))
    (ys := ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14))) (i := 100 + j) (by
      have hn : 80 ≤ 100 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 100 + j - 80 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (tableChunk_11 ++ tableChunk_12))
    (ys := (tableChunk_13 ++ tableChunk_14)) (i := 20 + j) (by
      have hn : 20 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := tableChunk_11)
    (ys := tableChunk_12) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_13 (j : ℕ) (hj : j < 20) :
    entryAt (266 + j) = tableChunk_13[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 266 + j - 6 = 260 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 260 + j) (by
      have hn : 260 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 260 + j) (by
      have hn : 140 ≤ 260 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 260 + j - 140 = 120 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := ((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)))
    (ys := ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14))) (i := 120 + j) (by
      have hn : 80 ≤ 120 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 120 + j - 80 = 40 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (tableChunk_11 ++ tableChunk_12))
    (ys := (tableChunk_13 ++ tableChunk_14)) (i := 40 + j) (by
      have hn : 40 ≤ 40 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 40 + j - 40 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := tableChunk_13)
    (ys := tableChunk_14) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_14 (j : ℕ) (hj : j < 20) :
    entryAt (286 + j) = tableChunk_14[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 286 + j - 6 = 280 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_left (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 280 + j) (by
      have hn : 280 + j < 300 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := ((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))))
    (ys := (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))) (i := 280 + j) (by
      have hn : 140 ≤ 280 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 280 + j - 140 = 140 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := ((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)))
    (ys := ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14))) (i := 140 + j) (by
      have hn : 80 ≤ 140 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 140 + j - 80 = 60 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (tableChunk_11 ++ tableChunk_12))
    (ys := (tableChunk_13 ++ tableChunk_14)) (i := 60 + j) (by
      have hn : 40 ≤ 60 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 60 + j - 40 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := tableChunk_13)
    (ys := tableChunk_14) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_15 (j : ℕ) (hj : j < 20) :
    entryAt (306 + j) = tableChunk_15[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 306 + j - 6 = 300 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 300 + j) (by
      have hn : 300 ≤ 300 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 300 + j - 300 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 0 + j) (by
      have hn : 0 + j < 160 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := ((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)))
    (ys := ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) (i := 0 + j) (by
      have hn : 0 + j < 80 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := (tableChunk_15 ++ tableChunk_16))
    (ys := (tableChunk_17 ++ tableChunk_18)) (i := 0 + j) (by
      have hn : 0 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := tableChunk_15)
    (ys := tableChunk_16) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_16 (j : ℕ) (hj : j < 20) :
    entryAt (326 + j) = tableChunk_16[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 326 + j - 6 = 320 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 320 + j) (by
      have hn : 300 ≤ 320 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 320 + j - 300 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 20 + j) (by
      have hn : 20 + j < 160 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := ((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)))
    (ys := ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) (i := 20 + j) (by
      have hn : 20 + j < 80 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := (tableChunk_15 ++ tableChunk_16))
    (ys := (tableChunk_17 ++ tableChunk_18)) (i := 20 + j) (by
      have hn : 20 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := tableChunk_15)
    (ys := tableChunk_16) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_17 (j : ℕ) (hj : j < 20) :
    entryAt (346 + j) = tableChunk_17[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 346 + j - 6 = 340 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 340 + j) (by
      have hn : 300 ≤ 340 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 340 + j - 300 = 40 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 40 + j) (by
      have hn : 40 + j < 160 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := ((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)))
    (ys := ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) (i := 40 + j) (by
      have hn : 40 + j < 80 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := (tableChunk_15 ++ tableChunk_16))
    (ys := (tableChunk_17 ++ tableChunk_18)) (i := 40 + j) (by
      have hn : 40 ≤ 40 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 40 + j - 40 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := tableChunk_17)
    (ys := tableChunk_18) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_18 (j : ℕ) (hj : j < 20) :
    entryAt (366 + j) = tableChunk_18[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 366 + j - 6 = 360 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 360 + j) (by
      have hn : 300 ≤ 360 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 360 + j - 300 = 60 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 60 + j) (by
      have hn : 60 + j < 160 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := ((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)))
    (ys := ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) (i := 60 + j) (by
      have hn : 60 + j < 80 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := (tableChunk_15 ++ tableChunk_16))
    (ys := (tableChunk_17 ++ tableChunk_18)) (i := 60 + j) (by
      have hn : 40 ≤ 60 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 60 + j - 40 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := tableChunk_17)
    (ys := tableChunk_18) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_19 (j : ℕ) (hj : j < 20) :
    entryAt (386 + j) = tableChunk_19[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 386 + j - 6 = 380 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 380 + j) (by
      have hn : 300 ≤ 380 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 380 + j - 300 = 80 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 80 + j) (by
      have hn : 80 + j < 160 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := ((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)))
    (ys := ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) (i := 80 + j) (by
      have hn : 80 ≤ 80 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 80 + j - 80 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (tableChunk_19 ++ tableChunk_20))
    (ys := (tableChunk_21 ++ tableChunk_22)) (i := 0 + j) (by
      have hn : 0 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := tableChunk_19)
    (ys := tableChunk_20) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_20 (j : ℕ) (hj : j < 20) :
    entryAt (406 + j) = tableChunk_20[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 406 + j - 6 = 400 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 400 + j) (by
      have hn : 300 ≤ 400 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 400 + j - 300 = 100 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 100 + j) (by
      have hn : 100 + j < 160 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := ((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)))
    (ys := ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) (i := 100 + j) (by
      have hn : 80 ≤ 100 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 100 + j - 80 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (tableChunk_19 ++ tableChunk_20))
    (ys := (tableChunk_21 ++ tableChunk_22)) (i := 20 + j) (by
      have hn : 20 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := tableChunk_19)
    (ys := tableChunk_20) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_21 (j : ℕ) (hj : j < 20) :
    entryAt (426 + j) = tableChunk_21[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 426 + j - 6 = 420 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 420 + j) (by
      have hn : 300 ≤ 420 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 420 + j - 300 = 120 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 120 + j) (by
      have hn : 120 + j < 160 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := ((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)))
    (ys := ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) (i := 120 + j) (by
      have hn : 80 ≤ 120 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 120 + j - 80 = 40 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (tableChunk_19 ++ tableChunk_20))
    (ys := (tableChunk_21 ++ tableChunk_22)) (i := 40 + j) (by
      have hn : 40 ≤ 40 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 40 + j - 40 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := tableChunk_21)
    (ys := tableChunk_22) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_22 (j : ℕ) (hj : j < 20) :
    entryAt (446 + j) = tableChunk_22[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 446 + j - 6 = 440 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 440 + j) (by
      have hn : 300 ≤ 440 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 440 + j - 300 = 140 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 140 + j) (by
      have hn : 140 + j < 160 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := ((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)))
    (ys := ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) (i := 140 + j) (by
      have hn : 80 ≤ 140 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 140 + j - 80 = 60 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (tableChunk_19 ++ tableChunk_20))
    (ys := (tableChunk_21 ++ tableChunk_22)) (i := 60 + j) (by
      have hn : 40 ≤ 60 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 60 + j - 40 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := tableChunk_21)
    (ys := tableChunk_22) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_23 (j : ℕ) (hj : j < 20) :
    entryAt (466 + j) = tableChunk_23[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 466 + j - 6 = 460 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 460 + j) (by
      have hn : 300 ≤ 460 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 460 + j - 300 = 160 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 160 + j) (by
      have hn : 160 ≤ 160 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 160 + j - 160 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := ((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)))
    (ys := ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))) (i := 0 + j) (by
      have hn : 0 + j < 80 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := (tableChunk_23 ++ tableChunk_24))
    (ys := (tableChunk_25 ++ tableChunk_26)) (i := 0 + j) (by
      have hn : 0 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := tableChunk_23)
    (ys := tableChunk_24) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_24 (j : ℕ) (hj : j < 20) :
    entryAt (486 + j) = tableChunk_24[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 486 + j - 6 = 480 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 480 + j) (by
      have hn : 300 ≤ 480 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 480 + j - 300 = 180 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 180 + j) (by
      have hn : 160 ≤ 180 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 180 + j - 160 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := ((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)))
    (ys := ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))) (i := 20 + j) (by
      have hn : 20 + j < 80 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := (tableChunk_23 ++ tableChunk_24))
    (ys := (tableChunk_25 ++ tableChunk_26)) (i := 20 + j) (by
      have hn : 20 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := tableChunk_23)
    (ys := tableChunk_24) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_25 (j : ℕ) (hj : j < 20) :
    entryAt (506 + j) = tableChunk_25[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 506 + j - 6 = 500 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 500 + j) (by
      have hn : 300 ≤ 500 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 500 + j - 300 = 200 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 200 + j) (by
      have hn : 160 ≤ 200 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 200 + j - 160 = 40 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := ((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)))
    (ys := ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))) (i := 40 + j) (by
      have hn : 40 + j < 80 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := (tableChunk_23 ++ tableChunk_24))
    (ys := (tableChunk_25 ++ tableChunk_26)) (i := 40 + j) (by
      have hn : 40 ≤ 40 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 40 + j - 40 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := tableChunk_25)
    (ys := tableChunk_26) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_26 (j : ℕ) (hj : j < 20) :
    entryAt (526 + j) = tableChunk_26[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 526 + j - 6 = 520 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 520 + j) (by
      have hn : 300 ≤ 520 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 520 + j - 300 = 220 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 220 + j) (by
      have hn : 160 ≤ 220 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 220 + j - 160 = 60 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := ((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)))
    (ys := ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))) (i := 60 + j) (by
      have hn : 60 + j < 80 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := (tableChunk_23 ++ tableChunk_24))
    (ys := (tableChunk_25 ++ tableChunk_26)) (i := 60 + j) (by
      have hn : 40 ≤ 60 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 60 + j - 40 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := tableChunk_25)
    (ys := tableChunk_26) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_27 (j : ℕ) (hj : j < 20) :
    entryAt (546 + j) = tableChunk_27[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 546 + j - 6 = 540 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 540 + j) (by
      have hn : 300 ≤ 540 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 540 + j - 300 = 240 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 240 + j) (by
      have hn : 160 ≤ 240 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 240 + j - 160 = 80 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := ((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)))
    (ys := ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))) (i := 80 + j) (by
      have hn : 80 ≤ 80 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 80 + j - 80 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (tableChunk_27 ++ tableChunk_28))
    (ys := (tableChunk_29 ++ tableChunk_30)) (i := 0 + j) (by
      have hn : 0 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_left (xs := tableChunk_27)
    (ys := tableChunk_28) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_28 (j : ℕ) (hj : j < 20) :
    entryAt (566 + j) = tableChunk_28[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 566 + j - 6 = 560 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 560 + j) (by
      have hn : 300 ≤ 560 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 560 + j - 300 = 260 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 260 + j) (by
      have hn : 160 ≤ 260 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 260 + j - 160 = 100 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := ((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)))
    (ys := ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))) (i := 100 + j) (by
      have hn : 80 ≤ 100 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 100 + j - 80 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := (tableChunk_27 ++ tableChunk_28))
    (ys := (tableChunk_29 ++ tableChunk_30)) (i := 20 + j) (by
      have hn : 20 + j < 40 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  rw [Array.getElem?_append_right (xs := tableChunk_27)
    (ys := tableChunk_28) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_29 (j : ℕ) (hj : j < 20) :
    entryAt (586 + j) = tableChunk_29[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 586 + j - 6 = 580 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 580 + j) (by
      have hn : 300 ≤ 580 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 580 + j - 300 = 280 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 280 + j) (by
      have hn : 160 ≤ 280 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 280 + j - 160 = 120 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := ((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)))
    (ys := ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))) (i := 120 + j) (by
      have hn : 80 ≤ 120 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 120 + j - 80 = 40 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (tableChunk_27 ++ tableChunk_28))
    (ys := (tableChunk_29 ++ tableChunk_30)) (i := 40 + j) (by
      have hn : 40 ≤ 40 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 40 + j - 40 = 0 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_left (xs := tableChunk_29)
    (ys := tableChunk_30) (i := 0 + j) (by
      have hn : 0 + j < 20 := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  try simp only [Nat.zero_add]
  try rfl

theorem entry_chunk_30 (j : ℕ) (hj : j < 10) :
    entryAt (606 + j) = tableChunk_30[j]?.getD emptyEntry := by
  unfold entryAt
  have hstart : 606 + j - 6 = 600 + j := by omega
  rw [hstart, table]
  rw [Array.getElem?_append_right (xs := (((tableChunk_0 ++ (tableChunk_1 ++ tableChunk_2)) ++ ((tableChunk_3 ++ tableChunk_4) ++ (tableChunk_5 ++ tableChunk_6))) ++ (((tableChunk_7 ++ tableChunk_8) ++ (tableChunk_9 ++ tableChunk_10)) ++ ((tableChunk_11 ++ tableChunk_12) ++ (tableChunk_13 ++ tableChunk_14)))))
    (ys := ((((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))) ++ (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))))) (i := 600 + j) (by
      have hn : 300 ≤ 600 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 600 + j - 300 = 300 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (((tableChunk_15 ++ tableChunk_16) ++ (tableChunk_17 ++ tableChunk_18)) ++ ((tableChunk_19 ++ tableChunk_20) ++ (tableChunk_21 ++ tableChunk_22))))
    (ys := (((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)) ++ ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30)))) (i := 300 + j) (by
      have hn : 160 ≤ 300 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 300 + j - 160 = 140 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := ((tableChunk_23 ++ tableChunk_24) ++ (tableChunk_25 ++ tableChunk_26)))
    (ys := ((tableChunk_27 ++ tableChunk_28) ++ (tableChunk_29 ++ tableChunk_30))) (i := 140 + j) (by
      have hn : 80 ≤ 140 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 140 + j - 80 = 60 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := (tableChunk_27 ++ tableChunk_28))
    (ys := (tableChunk_29 ++ tableChunk_30)) (i := 60 + j) (by
      have hn : 40 ≤ 60 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 60 + j - 40 = 20 + j := by omega
  try rw [hsub]
  rw [Array.getElem?_append_right (xs := tableChunk_29)
    (ys := tableChunk_30) (i := 20 + j) (by
      have hn : 20 ≤ 20 + j := by omega
      simpa only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd] using hn)]
  simp only [Array.size_append, chunk_size_0, chunk_size_1, chunk_size_2, chunk_size_3, chunk_size_4, chunk_size_5, chunk_size_6, chunk_size_7, chunk_size_8, chunk_size_9, chunk_size_10, chunk_size_11, chunk_size_12, chunk_size_13, chunk_size_14, chunk_size_15, chunk_size_16, chunk_size_17, chunk_size_18, chunk_size_19, chunk_size_20, chunk_size_21, chunk_size_22, chunk_size_23, chunk_size_24, chunk_size_25, chunk_size_26, chunk_size_27, chunk_size_28, chunk_size_29, chunk_size_30, Nat.reduceAdd]
  have hsub : 20 + j - 20 = 0 + j := by omega
  try rw [hsub]
  try simp only [Nat.zero_add]
  try rfl

def data_0 : RowData := ⟨{(1, 0), (2, 0), (3, 0), (3, 1), (4, 1)}, {(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)}, 1⟩
theorem row_0 : rowAt 0 = data_0 := by apply row_ext <;> decide +kernel
theorem good_0 : Good (rowAt 0) := by
  rw [row_0]
  unfold Good
  decide +kernel

def data_1 : RowData := ⟨{(-1, 0), (1, 0), (2, 0), (2, 1), (3, 1)}, {(-1, 0), (0, 0), (1, 0), (2, 0), (2, 1), (3, 1)}, 1⟩
theorem row_1 : rowAt 1 = data_1 := by apply row_ext <;> decide +kernel
theorem good_1 : Good (rowAt 1) := by
  rw [row_1]
  unfold Good
  decide +kernel

def data_2 : RowData := ⟨{(-2, 0), (-1, 0), (1, 0), (1, 1), (2, 1)}, {(-2, 0), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)}, 1⟩
theorem row_2 : rowAt 2 = data_2 := by apply row_ext <;> decide +kernel
theorem good_2 : Good (rowAt 2) := by
  rw [row_2]
  unfold Good
  decide +kernel

def data_3 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0), (0, 1), (1, 1)}, {(-3, 0), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 1)}, 1⟩
theorem row_3 : rowAt 3 = data_3 := by apply row_ext <;> decide +kernel
theorem good_3 : Good (rowAt 3) := by
  rw [row_3]
  unfold Good
  decide +kernel

def data_4 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (0, -1), (1, 0)}, {(-3, -1), (-2, -1), (-1, -1), (0, -1), (0, 0), (1, 0)}, 1⟩
theorem row_4 : rowAt 4 = data_4 := by apply row_ext <;> decide +kernel
theorem good_4 : Good (rowAt 4) := by
  rw [row_4]
  unfold Good
  decide +kernel

def data_5 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, 0)}, 1⟩
theorem row_5 : rowAt 5 = data_5 := by apply row_ext <;> decide +kernel
theorem good_5 : Good (rowAt 5) := by
  rw [row_5]
  unfold Good
  decide +kernel

def data_6 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, 0)}, 2⟩
theorem entry_6_checked : entryAt 6 = entry_6 := by
  rw [entry_chunk_0 0 (by decide)]
  decide +kernel
theorem row_6 : rowAt 6 = data_6 := by
  rw [rowAt, dif_neg (by decide : ¬ 6 < 6), entry_6_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0)] = data_6
  rw [row_0]
  apply row_ext <;> decide +kernel
theorem entry_good_6 : EntryGood 6 := by
  unfold EntryGood
  rw [entry_6_checked]
  decide +kernel
theorem good_6 : Good (rowAt 6) := by
  rw [row_6]
  unfold Good
  decide +kernel

def data_7 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-1, -1), (0, -1)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0)}, 3⟩
theorem entry_7_checked : entryAt 7 = entry_7 := by
  rw [entry_chunk_0 1 (by decide)]
  decide +kernel
theorem row_7 : rowAt 7 = data_7 := by
  rw [rowAt, dif_neg (by decide : ¬ 7 < 6), entry_7_checked]
  change forkRow [placeRow ⟨4, 0, 3, 4⟩ (rowAt 4), placeRow ⟨6, 0, 5, 4⟩ (rowAt 6)] = data_7
  rw [row_4, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_7 : EntryGood 7 := by
  unfold EntryGood
  rw [entry_7_checked]
  decide +kernel
theorem good_7 : Good (rowAt 7) := by
  rw [row_7]
  unfold Good
  decide +kernel

def data_8 : RowData := ⟨{(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)}, {(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 3⟩
theorem entry_8_checked : entryAt 8 = entry_8 := by
  rw [entry_chunk_0 2 (by decide)]
  decide +kernel
theorem row_8 : rowAt 8 = data_8 := by
  rw [rowAt, dif_neg (by decide : ¬ 8 < 6), entry_8_checked]
  change forkRow [placeRow ⟨0, 4, 8, 3⟩ (rowAt 0), placeRow ⟨6, 4, 3, 4⟩ (rowAt 6)] = data_8
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_8 : EntryGood 8 := by
  unfold EntryGood
  rw [entry_8_checked]
  decide +kernel
theorem good_8 : Good (rowAt 8) := by
  rw [row_8]
  unfold Good
  decide +kernel

def data_9 : RowData := ⟨{(-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (1, 0)}, 3⟩
theorem entry_9_checked : entryAt 9 = entry_9 := by
  rw [entry_chunk_0 3 (by decide)]
  decide +kernel
theorem row_9 : rowAt 9 = data_9 := by
  rw [rowAt, dif_neg (by decide : ¬ 9 < 6), entry_9_checked]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (rowAt 0), placeRow ⟨6, 4, 0, 5⟩ (rowAt 6)] = data_9
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_9 : EntryGood 9 := by
  unfold EntryGood
  rw [entry_9_checked]
  decide +kernel
theorem good_9 : Good (rowAt 9) := by
  rw [row_9]
  unfold Good
  decide +kernel

def data_10 : RowData := ⟨{(-4, -1), (-3, -1), (-3, 0), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0)}, 2⟩
theorem entry_10_checked : entryAt 10 = entry_10 := by
  rw [entry_chunk_0 4 (by decide)]
  decide +kernel
theorem row_10 : rowAt 10 = data_10 := by
  rw [rowAt, dif_neg (by decide : ¬ 10 < 6), entry_10_checked]
  change forkRow [placeRow ⟨2, 0, 2, 3⟩ (rowAt 2), placeRow ⟨2, 6, 2, 4⟩ (rowAt 2)] = data_10
  rw [row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_10 : EntryGood 10 := by
  unfold EntryGood
  rw [entry_10_checked]
  decide +kernel
theorem good_10 : Good (rowAt 10) := by
  rw [row_10]
  unfold Good
  decide +kernel

def data_11 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (1, 0), (2, 0)}, {(-2, -1), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 0), (2, 0)}, 3⟩
theorem entry_11_checked : entryAt 11 = entry_11 := by
  rw [entry_chunk_0 5 (by decide)]
  decide +kernel
theorem row_11 : rowAt 11 = data_11 := by
  rw [rowAt, dif_neg (by decide : ¬ 11 < 6), entry_11_checked]
  change forkRow [placeRow ⟨6, 4, 2, 5⟩ (rowAt 6), placeRow ⟨6, 6, 2, 3⟩ (rowAt 6)] = data_11
  rw [row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_11 : EntryGood 11 := by
  unfold EntryGood
  rw [entry_11_checked]
  decide +kernel
theorem good_11 : Good (rowAt 11) := by
  rw [row_11]
  unfold Good
  decide +kernel

#check row_11
end OAI.SnakyCertificate.MilestoneChecks
