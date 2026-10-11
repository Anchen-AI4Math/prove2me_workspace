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

def data_12 : RowData := ⟨{(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)}, 2⟩
theorem entry_12_checked : entryAt 12 = entry_12 := by
  rw [entry_chunk_0 6 (by decide)]
  decide +kernel
theorem row_12 : rowAt 12 = data_12 := by
  rw [rowAt, dif_neg (by decide : ¬ 12 < 6), entry_12_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨0, 0, 0, 3⟩ (rowAt 0)] = data_12
  rw [row_0]
  apply row_ext <;> decide +kernel
theorem entry_good_12 : EntryGood 12 := by
  unfold EntryGood
  rw [entry_12_checked]
  decide +kernel
theorem good_12 : Good (rowAt 12) := by
  rw [row_12]
  unfold Good
  decide +kernel

def data_13 : RowData := ⟨{(-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 0)}, 3⟩
theorem entry_13_checked : entryAt 13 = entry_13 := by
  rw [entry_chunk_0 7 (by decide)]
  decide +kernel
theorem row_13 : rowAt 13 = data_13 := by
  rw [rowAt, dif_neg (by decide : ¬ 13 < 6), entry_13_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨6, 4, 0, 5⟩ (rowAt 6)] = data_13
  rw [row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_13 : EntryGood 13 := by
  unfold EntryGood
  rw [entry_13_checked]
  decide +kernel
theorem good_13 : Good (rowAt 13) := by
  rw [row_13]
  unfold Good
  decide +kernel

def data_14 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)}, 2⟩
theorem entry_14_checked : entryAt 14 = entry_14 := by
  rw [entry_chunk_0 8 (by decide)]
  decide +kernel
theorem row_14 : rowAt 14 = data_14 := by
  rw [rowAt, dif_neg (by decide : ¬ 14 < 6), entry_14_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨3, 6, 1, 4⟩ (rowAt 3)] = data_14
  rw [row_0, row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_14 : EntryGood 14 := by
  unfold EntryGood
  rw [entry_14_checked]
  decide +kernel
theorem good_14 : Good (rowAt 14) := by
  rw [row_14]
  unfold Good
  decide +kernel

def data_15 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0), (1, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)}, 2⟩
theorem entry_15_checked : entryAt 15 = entry_15 := by
  rw [entry_chunk_0 9 (by decide)]
  decide +kernel
theorem row_15 : rowAt 15 = data_15 := by
  rw [rowAt, dif_neg (by decide : ¬ 15 < 6), entry_15_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨3, 6, 2, 4⟩ (rowAt 3)] = data_15
  rw [row_0, row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_15 : EntryGood 15 := by
  unfold EntryGood
  rw [entry_15_checked]
  decide +kernel
theorem good_15 : Good (rowAt 15) := by
  rw [row_15]
  unfold Good
  decide +kernel

def data_16 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, 0), (2, 0)}, {(-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0), (3, 0)}, 2⟩
theorem entry_16_checked : entryAt 16 = entry_16 := by
  rw [entry_chunk_0 10 (by decide)]
  decide +kernel
theorem row_16 : rowAt 16 = data_16 := by
  rw [rowAt, dif_neg (by decide : ¬ 16 < 6), entry_16_checked]
  change forkRow [placeRow ⟨3, 6, 3, 4⟩ (rowAt 3), placeRow ⟨0, 6, 7, 4⟩ (rowAt 0)] = data_16
  rw [row_3, row_0]
  apply row_ext <;> decide +kernel
theorem entry_good_16 : EntryGood 16 := by
  unfold EntryGood
  rw [entry_16_checked]
  decide +kernel
theorem good_16 : Good (rowAt 16) := by
  rw [row_16]
  unfold Good
  decide +kernel

def data_17 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)}, 2⟩
theorem entry_17_checked : entryAt 17 = entry_17 := by
  rw [entry_chunk_0 11 (by decide)]
  decide +kernel
theorem row_17 : rowAt 17 = data_17 := by
  rw [rowAt, dif_neg (by decide : ¬ 17 < 6), entry_17_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨3, 0, 3, 3⟩ (rowAt 3)] = data_17
  rw [row_0, row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_17 : EntryGood 17 := by
  unfold EntryGood
  rw [entry_17_checked]
  decide +kernel
theorem good_17 : Good (rowAt 17) := by
  rw [row_17]
  unfold Good
  decide +kernel

def data_18 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0), (1, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0)}, 2⟩
theorem entry_18_checked : entryAt 18 = entry_18 := by
  rw [entry_chunk_0 12 (by decide)]
  decide +kernel
theorem row_18 : rowAt 18 = data_18 := by
  rw [rowAt, dif_neg (by decide : ¬ 18 < 6), entry_18_checked]
  change forkRow [placeRow ⟨3, 6, 2, 4⟩ (rowAt 3), placeRow ⟨3, 0, 4, 3⟩ (rowAt 3)] = data_18
  rw [row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_18 : EntryGood 18 := by
  unfold EntryGood
  rw [entry_18_checked]
  decide +kernel
theorem good_18 : Good (rowAt 18) := by
  rw [row_18]
  unfold Good
  decide +kernel

def data_19 : RowData := ⟨{(-2, 0), (-2, 1), (-1, 0), (1, 0), (1, 1)}, {(-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)}, 3⟩
theorem entry_19_checked : entryAt 19 = entry_19 := by
  rw [entry_chunk_0 13 (by decide)]
  decide +kernel
theorem row_19 : rowAt 19 = data_19 := by
  rw [rowAt, dif_neg (by decide : ¬ 19 < 6), entry_19_checked]
  change forkRow [placeRow ⟨6, 4, 1, 5⟩ (rowAt 6), placeRow ⟨6, 0, 6, 5⟩ (rowAt 6)] = data_19
  rw [row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_19 : EntryGood 19 := by
  unfold EntryGood
  rw [entry_19_checked]
  decide +kernel
theorem good_19 : Good (rowAt 19) := by
  rw [row_19]
  unfold Good
  decide +kernel

def data_20 : RowData := ⟨{(-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 1)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 1)}, 3⟩
theorem entry_20_checked : entryAt 20 = entry_20 := by
  rw [entry_chunk_0 14 (by decide)]
  decide +kernel
theorem row_20 : rowAt 20 = data_20 := by
  rw [rowAt, dif_neg (by decide : ¬ 20 < 6), entry_20_checked]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (rowAt 6), placeRow ⟨6, 0, 5, 5⟩ (rowAt 6)] = data_20
  rw [row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_20 : EntryGood 20 := by
  unfold EntryGood
  rw [entry_20_checked]
  decide +kernel
theorem good_20 : Good (rowAt 20) := by
  rw [row_20]
  unfold Good
  decide +kernel

def data_21 : RowData := ⟨{(-3, -1), (-2, 0), (-1, 0), (1, 0), (1, 1)}, {(-3, -1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)}, 3⟩
theorem entry_21_checked : entryAt 21 = entry_21 := by
  rw [entry_chunk_0 15 (by decide)]
  decide +kernel
theorem row_21 : rowAt 21 = data_21 := by
  rw [rowAt, dif_neg (by decide : ¬ 21 < 6), entry_21_checked]
  change forkRow [placeRow ⟨4, 6, 2, 3⟩ (rowAt 4), placeRow ⟨6, 0, 6, 5⟩ (rowAt 6)] = data_21
  rw [row_4, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_21 : EntryGood 21 := by
  unfold EntryGood
  rw [entry_21_checked]
  decide +kernel
theorem good_21 : Good (rowAt 21) := by
  rw [row_21]
  unfold Good
  decide +kernel

def data_22 : RowData := ⟨{(-2, 0), (-1, 0), (0, 1), (1, 1), (2, 1)}, {(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1)}, 2⟩
theorem entry_22_checked : entryAt 22 = entry_22 := by
  rw [entry_chunk_0 16 (by decide)]
  decide +kernel
theorem row_22 : rowAt 22 = data_22 := by
  rw [rowAt, dif_neg (by decide : ¬ 22 < 6), entry_22_checked]
  change forkRow [placeRow ⟨0, 6, 7, 5⟩ (rowAt 0), placeRow ⟨3, 0, 5, 4⟩ (rowAt 3)] = data_22
  rw [row_0, row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_22 : EntryGood 22 := by
  unfold EntryGood
  rw [entry_22_checked]
  decide +kernel
theorem good_22 : Good (rowAt 22) := by
  rw [row_22]
  unfold Good
  decide +kernel

def data_23 : RowData := ⟨{(-2, -1), (-1, -1), (-1, 0), (0, -1), (1, 0)}, {(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)}, 2⟩
theorem entry_23_checked : entryAt 23 = entry_23 := by
  rw [entry_chunk_0 17 (by decide)]
  decide +kernel
theorem row_23 : rowAt 23 = data_23 := by
  rw [rowAt, dif_neg (by decide : ¬ 23 < 6), entry_23_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨0, 0, 1, 3⟩ (rowAt 0)] = data_23
  rw [row_0]
  apply row_ext <;> decide +kernel
theorem entry_good_23 : EntryGood 23 := by
  unfold EntryGood
  rw [entry_23_checked]
  decide +kernel
theorem good_23 : Good (rowAt 23) := by
  rw [row_23]
  unfold Good
  decide +kernel

def data_24 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)}, 3⟩
theorem entry_24_checked : entryAt 24 = entry_24 := by
  rw [entry_chunk_0 18 (by decide)]
  decide +kernel
theorem row_24 : rowAt 24 = data_24 := by
  rw [rowAt, dif_neg (by decide : ¬ 24 < 6), entry_24_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨17, 0, 5, 4⟩ (rowAt 17)] = data_24
  rw [row_0, row_17]
  apply row_ext <;> decide +kernel
theorem entry_good_24 : EntryGood 24 := by
  unfold EntryGood
  rw [entry_24_checked]
  decide +kernel
theorem good_24 : Good (rowAt 24) := by
  rw [row_24]
  unfold Good
  decide +kernel

def data_25 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)}, 3⟩
theorem entry_25_checked : entryAt 25 = entry_25 := by
  rw [entry_chunk_0 19 (by decide)]
  decide +kernel
theorem row_25 : rowAt 25 = data_25 := by
  rw [rowAt, dif_neg (by decide : ¬ 25 < 6), entry_25_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨14, 0, 5, 4⟩ (rowAt 14)] = data_25
  rw [row_0, row_14]
  apply row_ext <;> decide +kernel
theorem entry_good_25 : EntryGood 25 := by
  unfold EntryGood
  rw [entry_25_checked]
  decide +kernel
theorem good_25 : Good (rowAt 25) := by
  rw [row_25]
  unfold Good
  decide +kernel

def data_26 : RowData := ⟨{(-2, 0), (-2, 1), (-1, 0), (-1, 1), (1, 0), (1, 1)}, {(-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1)}, 3⟩
theorem entry_26_checked : entryAt 26 = entry_26 := by
  rw [entry_chunk_1 0 (by decide)]
  decide +kernel
theorem row_26 : rowAt 26 = data_26 := by
  rw [rowAt, dif_neg (by decide : ¬ 26 < 6), entry_26_checked]
  change forkRow [placeRow ⟨0, 4, 6, 4⟩ (rowAt 0), placeRow ⟨6, 0, 6, 5⟩ (rowAt 6)] = data_26
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_26 : EntryGood 26 := by
  unfold EntryGood
  rw [entry_26_checked]
  decide +kernel
theorem good_26 : Good (rowAt 26) := by
  rw [row_26]
  unfold Good
  decide +kernel

def data_27 : RowData := ⟨{(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, 0)}, {(-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)}, 3⟩
theorem entry_27_checked : entryAt 27 = entry_27 := by
  rw [entry_chunk_1 1 (by decide)]
  decide +kernel
theorem row_27 : rowAt 27 = data_27 := by
  rw [rowAt, dif_neg (by decide : ¬ 27 < 6), entry_27_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨6, 4, 0, 5⟩ (rowAt 6)] = data_27
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_27 : EntryGood 27 := by
  unfold EntryGood
  rw [entry_27_checked]
  decide +kernel
theorem good_27 : Good (rowAt 27) := by
  rw [row_27]
  unfold Good
  decide +kernel

def data_28 : RowData := ⟨{(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, 0)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)}, 3⟩
theorem entry_28_checked : entryAt 28 = entry_28 := by
  rw [entry_chunk_1 2 (by decide)]
  decide +kernel
theorem row_28 : rowAt 28 = data_28 := by
  rw [rowAt, dif_neg (by decide : ¬ 28 < 6), entry_28_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨0, 6, 6, 4⟩ (rowAt 0)] = data_28
  rw [row_6, row_0]
  apply row_ext <;> decide +kernel
theorem entry_good_28 : EntryGood 28 := by
  unfold EntryGood
  rw [entry_28_checked]
  decide +kernel
theorem good_28 : Good (rowAt 28) := by
  rw [row_28]
  unfold Good
  decide +kernel

def data_29 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (4, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 3⟩
theorem entry_29_checked : entryAt 29 = entry_29 := by
  rw [entry_chunk_1 3 (by decide)]
  decide +kernel
theorem row_29 : rowAt 29 = data_29 := by
  rw [rowAt, dif_neg (by decide : ¬ 29 < 6), entry_29_checked]
  change forkRow [placeRow ⟨1, 4, 7, 3⟩ (rowAt 1), placeRow ⟨6, 3, 4, 5⟩ (rowAt 6)] = data_29
  rw [row_1, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_29 : EntryGood 29 := by
  unfold EntryGood
  rw [entry_29_checked]
  decide +kernel
theorem good_29 : Good (rowAt 29) := by
  rw [row_29]
  unfold Good
  decide +kernel

def data_30 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, 0)}, {(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0), (3, 0)}, 3⟩
theorem entry_30_checked : entryAt 30 = entry_30 := by
  rw [entry_chunk_1 4 (by decide)]
  decide +kernel
theorem row_30 : rowAt 30 = data_30 := by
  rw [rowAt, dif_neg (by decide : ¬ 30 < 6), entry_30_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨14, 0, 6, 4⟩ (rowAt 14)] = data_30
  rw [row_0, row_14]
  apply row_ext <;> decide +kernel
theorem entry_good_30 : EntryGood 30 := by
  unfold EntryGood
  rw [entry_30_checked]
  decide +kernel
theorem good_30 : Good (rowAt 30) := by
  rw [row_30]
  unfold Good
  decide +kernel

def data_31 : RowData := ⟨{(-2, 0), (-1, 0), (0, 1), (1, 1)}, {(-3, 0), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1)}, 3⟩
theorem entry_31_checked : entryAt 31 = entry_31 := by
  rw [entry_chunk_1 5 (by decide)]
  decide +kernel
theorem row_31 : rowAt 31 = data_31 := by
  rw [rowAt, dif_neg (by decide : ¬ 31 < 6), entry_31_checked]
  change forkRow [placeRow ⟨0, 0, 1, 4⟩ (rowAt 0), placeRow ⟨17, 0, 6, 5⟩ (rowAt 17)] = data_31
  rw [row_0, row_17]
  apply row_ext <;> decide +kernel
theorem entry_good_31 : EntryGood 31 := by
  unfold EntryGood
  rw [entry_31_checked]
  decide +kernel
theorem good_31 : Good (rowAt 31) := by
  rw [row_31]
  unfold Good
  decide +kernel

#check row_31
def data_32 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 3⟩
theorem entry_32_checked : entryAt 32 = entry_32 := by
  rw [entry_chunk_1 6 (by decide)]
  decide +kernel
theorem row_32 : rowAt 32 = data_32 := by
  rw [rowAt, dif_neg (by decide : ¬ 32 < 6), entry_32_checked]
  change forkRow [placeRow ⟨0, 4, 8, 3⟩ (rowAt 0), placeRow ⟨6, 3, 4, 5⟩ (rowAt 6)] = data_32
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_32 : EntryGood 32 := by
  unfold EntryGood
  rw [entry_32_checked]
  decide +kernel
theorem good_32 : Good (rowAt 32) := by
  rw [row_32]
  unfold Good
  decide +kernel

def data_33 : RowData := ⟨{(-1, 0), (1, 0), (1, 1), (2, 1)}, {(-2, 0), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1), (4, 1)}, 3⟩
theorem entry_33_checked : entryAt 33 = entry_33 := by
  rw [entry_chunk_1 7 (by decide)]
  decide +kernel
theorem row_33 : rowAt 33 = data_33 := by
  rw [rowAt, dif_neg (by decide : ¬ 33 < 6), entry_33_checked]
  change forkRow [placeRow ⟨0, 0, 2, 4⟩ (rowAt 0), placeRow ⟨17, 0, 7, 5⟩ (rowAt 17)] = data_33
  rw [row_0, row_17]
  apply row_ext <;> decide +kernel
theorem entry_good_33 : EntryGood 33 := by
  unfold EntryGood
  rw [entry_33_checked]
  decide +kernel
theorem good_33 : Good (rowAt 33) := by
  rw [row_33]
  unfold Good
  decide +kernel

def data_34 : RowData := ⟨{(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, 0)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)}, 3⟩
theorem entry_34_checked : entryAt 34 = entry_34 := by
  rw [entry_chunk_1 8 (by decide)]
  decide +kernel
theorem row_34 : rowAt 34 = data_34 := by
  rw [rowAt, dif_neg (by decide : ¬ 34 < 6), entry_34_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨1, 6, 5, 4⟩ (rowAt 1)] = data_34
  rw [row_6, row_1]
  apply row_ext <;> decide +kernel
theorem entry_good_34 : EntryGood 34 := by
  unfold EntryGood
  rw [entry_34_checked]
  decide +kernel
theorem good_34 : Good (rowAt 34) := by
  rw [row_34]
  unfold Good
  decide +kernel

def data_35 : RowData := ⟨{(-1, 0), (1, 0), (1, 1), (2, 1)}, {(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (4, 1)}, 3⟩
theorem entry_35_checked : entryAt 35 = entry_35 := by
  rw [entry_chunk_1 9 (by decide)]
  decide +kernel
theorem row_35 : rowAt 35 = data_35 := by
  rw [rowAt, dif_neg (by decide : ¬ 35 < 6), entry_35_checked]
  change forkRow [placeRow ⟨0, 0, 2, 4⟩ (rowAt 0), placeRow ⟨14, 0, 7, 5⟩ (rowAt 14)] = data_35
  rw [row_0, row_14]
  apply row_ext <;> decide +kernel
theorem entry_good_35 : EntryGood 35 := by
  unfold EntryGood
  rw [entry_35_checked]
  decide +kernel
theorem good_35 : Good (rowAt 35) := by
  rw [row_35]
  unfold Good
  decide +kernel

def data_36 : RowData := ⟨{(1, 0), (2, 0), (2, 1), (3, 1)}, {(-1, 0), (0, 0), (1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1), (5, 1)}, 3⟩
theorem entry_36_checked : entryAt 36 = entry_36 := by
  rw [entry_chunk_1 10 (by decide)]
  decide +kernel
theorem row_36 : rowAt 36 = data_36 := by
  rw [rowAt, dif_neg (by decide : ¬ 36 < 6), entry_36_checked]
  change forkRow [placeRow ⟨0, 0, 3, 4⟩ (rowAt 0), placeRow ⟨17, 0, 8, 5⟩ (rowAt 17)] = data_36
  rw [row_0, row_17]
  apply row_ext <;> decide +kernel
theorem entry_good_36 : EntryGood 36 := by
  unfold EntryGood
  rw [entry_36_checked]
  decide +kernel
theorem good_36 : Good (rowAt 36) := by
  rw [row_36]
  unfold Good
  decide +kernel

def data_37 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (3, -1), (4, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 3⟩
theorem entry_37_checked : entryAt 37 = entry_37 := by
  rw [entry_chunk_1 11 (by decide)]
  decide +kernel
theorem row_37 : rowAt 37 = data_37 := by
  rw [rowAt, dif_neg (by decide : ¬ 37 < 6), entry_37_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨2, 4, 6, 3⟩ (rowAt 2)] = data_37
  rw [row_6, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_37 : EntryGood 37 := by
  unfold EntryGood
  rw [entry_37_checked]
  decide +kernel
theorem good_37 : Good (rowAt 37) := by
  rw [row_37]
  unfold Good
  decide +kernel

def data_38 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)}, 3⟩
theorem entry_38_checked : entryAt 38 = entry_38 := by
  rw [entry_chunk_1 12 (by decide)]
  decide +kernel
theorem row_38 : rowAt 38 = data_38 := by
  rw [rowAt, dif_neg (by decide : ¬ 38 < 6), entry_38_checked]
  change forkRow [placeRow ⟨3, 0, 3, 3⟩ (rowAt 3), placeRow ⟨16, 0, 2, 4⟩ (rowAt 16)] = data_38
  rw [row_3, row_16]
  apply row_ext <;> decide +kernel
theorem entry_good_38 : EntryGood 38 := by
  unfold EntryGood
  rw [entry_38_checked]
  decide +kernel
theorem good_38 : Good (rowAt 38) := by
  rw [row_38]
  unfold Good
  decide +kernel

def data_39 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, 0)}, {(-3, -1), (-2, -1), (-1, -1), (0, -1), (0, 0), (1, -1), (1, 0), (2, 0), (3, 0)}, 3⟩
theorem entry_39_checked : entryAt 39 = entry_39 := by
  rw [entry_chunk_1 13 (by decide)]
  decide +kernel
theorem row_39 : rowAt 39 = data_39 := by
  rw [rowAt, dif_neg (by decide : ¬ 39 < 6), entry_39_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨17, 0, 6, 4⟩ (rowAt 17)] = data_39
  rw [row_0, row_17]
  apply row_ext <;> decide +kernel
theorem entry_good_39 : EntryGood 39 := by
  unfold EntryGood
  rw [entry_39_checked]
  decide +kernel
theorem good_39 : Good (rowAt 39) := by
  rw [row_39]
  unfold Good
  decide +kernel

def data_40 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (1, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)}, 3⟩
theorem entry_40_checked : entryAt 40 = entry_40 := by
  rw [entry_chunk_1 14 (by decide)]
  decide +kernel
theorem row_40 : rowAt 40 = data_40 := by
  rw [rowAt, dif_neg (by decide : ¬ 40 < 6), entry_40_checked]
  change forkRow [placeRow ⟨3, 0, 4, 3⟩ (rowAt 3), placeRow ⟨16, 0, 3, 4⟩ (rowAt 16)] = data_40
  rw [row_3, row_16]
  apply row_ext <;> decide +kernel
theorem entry_good_40 : EntryGood 40 := by
  unfold EntryGood
  rw [entry_40_checked]
  decide +kernel
theorem good_40 : Good (rowAt 40) := by
  rw [row_40]
  unfold Good
  decide +kernel

def data_41 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1), (1, -1), (3, -1)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (2, -1), (3, -1)}, 3⟩
theorem entry_41_checked : entryAt 41 = entry_41 := by
  rw [entry_chunk_1 15 (by decide)]
  decide +kernel
theorem row_41 : rowAt 41 = data_41 := by
  rw [rowAt, dif_neg (by decide : ¬ 41 < 6), entry_41_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨1, 4, 6, 3⟩ (rowAt 1)] = data_41
  rw [row_6, row_1]
  apply row_ext <;> decide +kernel
theorem entry_good_41 : EntryGood 41 := by
  unfold EntryGood
  rw [entry_41_checked]
  decide +kernel
theorem good_41 : Good (rowAt 41) := by
  rw [row_41]
  unfold Good
  decide +kernel

def data_42 : RowData := ⟨{(-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (1, 0)}, {(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)}, 3⟩
theorem entry_42_checked : entryAt 42 = entry_42 := by
  rw [entry_chunk_1 16 (by decide)]
  decide +kernel
theorem row_42 : rowAt 42 = data_42 := by
  rw [rowAt, dif_neg (by decide : ¬ 42 < 6), entry_42_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨6, 4, 1, 5⟩ (rowAt 6)] = data_42
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_42 : EntryGood 42 := by
  unfold EntryGood
  rw [entry_42_checked]
  decide +kernel
theorem good_42 : Good (rowAt 42) := by
  rw [row_42]
  unfold Good
  decide +kernel

def data_43 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (2, -1), (3, -1)}, 3⟩
theorem entry_43_checked : entryAt 43 = entry_43 := by
  rw [entry_chunk_1 17 (by decide)]
  decide +kernel
theorem row_43 : rowAt 43 = data_43 := by
  rw [rowAt, dif_neg (by decide : ¬ 43 < 6), entry_43_checked]
  change forkRow [placeRow ⟨2, 4, 5, 3⟩ (rowAt 2), placeRow ⟨6, 3, 3, 5⟩ (rowAt 6)] = data_43
  rw [row_2, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_43 : EntryGood 43 := by
  unfold EntryGood
  rw [entry_43_checked]
  decide +kernel
theorem good_43 : Good (rowAt 43) := by
  rw [row_43]
  unfold Good
  decide +kernel

def data_44 : RowData := ⟨{(-4, 0), (-4, 1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)}, 4⟩
theorem entry_44_checked : entryAt 44 = entry_44 := by
  rw [entry_chunk_1 18 (by decide)]
  decide +kernel
theorem row_44 : rowAt 44 = data_44 := by
  rw [rowAt, dif_neg (by decide : ¬ 44 < 6), entry_44_checked]
  change forkRow [placeRow ⟨4, 4, 1, 5⟩ (rowAt 4), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_44
  rw [row_4, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_44 : EntryGood 44 := by
  unfold EntryGood
  rw [entry_44_checked]
  decide +kernel
theorem good_44 : Good (rowAt 44) := by
  rw [row_44]
  unfold Good
  decide +kernel

def data_45 : RowData := ⟨{(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-1, 0)}, {(-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)}, 4⟩
theorem entry_45_checked : entryAt 45 = entry_45 := by
  rw [entry_chunk_1 19 (by decide)]
  decide +kernel
theorem row_45 : rowAt 45 = data_45 := by
  rw [rowAt, dif_neg (by decide : ¬ 45 < 6), entry_45_checked]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (rowAt 6), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_45
  rw [row_6, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_45 : EntryGood 45 := by
  unfold EntryGood
  rw [entry_45_checked]
  decide +kernel
theorem good_45 : Good (rowAt 45) := by
  rw [row_45]
  unfold Good
  decide +kernel

def data_46 : RowData := ⟨{(-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)}, 4⟩
theorem entry_46_checked : entryAt 46 = entry_46 := by
  rw [entry_chunk_2 0 (by decide)]
  decide +kernel
theorem row_46 : rowAt 46 = data_46 := by
  rw [rowAt, dif_neg (by decide : ¬ 46 < 6), entry_46_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_46
  rw [row_6, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_46 : EntryGood 46 := by
  unfold EntryGood
  rw [entry_46_checked]
  decide +kernel
theorem good_46 : Good (rowAt 46) := by
  rw [row_46]
  unfold Good
  decide +kernel

def data_47 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1), (1, 0), (2, -1), (2, 0)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (2, -1), (2, 0), (3, -1)}, 3⟩
theorem entry_47_checked : entryAt 47 = entry_47 := by
  rw [entry_chunk_2 1 (by decide)]
  decide +kernel
theorem row_47 : rowAt 47 = data_47 := by
  rw [rowAt, dif_neg (by decide : ¬ 47 < 6), entry_47_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨6, 2, 7, 3⟩ (rowAt 6)] = data_47
  rw [row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_47 : EntryGood 47 := by
  unfold EntryGood
  rw [entry_47_checked]
  decide +kernel
theorem good_47 : Good (rowAt 47) := by
  rw [row_47]
  unfold Good
  decide +kernel

def data_48 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (4, -1)}, 3⟩
theorem entry_48_checked : entryAt 48 = entry_48 := by
  rw [entry_chunk_2 2 (by decide)]
  decide +kernel
theorem row_48 : rowAt 48 = data_48 := by
  rw [rowAt, dif_neg (by decide : ¬ 48 < 6), entry_48_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨6, 2, 8, 3⟩ (rowAt 6)] = data_48
  rw [row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_48 : EntryGood 48 := by
  unfold EntryGood
  rw [entry_48_checked]
  decide +kernel
theorem good_48 : Good (rowAt 48) := by
  rw [row_48]
  unfold Good
  decide +kernel

def data_49 : RowData := ⟨{(-1, -4), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -4), (-1, -3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1)}, 4⟩
theorem entry_49_checked : entryAt 49 = entry_49 := by
  rw [entry_chunk_2 3 (by decide)]
  decide +kernel
theorem row_49 : rowAt 49 = data_49 := by
  rw [rowAt, dif_neg (by decide : ¬ 49 < 6), entry_49_checked]
  change forkRow [placeRow ⟨4, 7, 3, 1⟩ (rowAt 4), placeRow ⟨7, 1, 5, 4⟩ (rowAt 7)] = data_49
  rw [row_4, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_49 : EntryGood 49 := by
  unfold EntryGood
  rw [entry_49_checked]
  decide +kernel
theorem good_49 : Good (rowAt 49) := by
  rw [row_49]
  unfold Good
  decide +kernel

def data_50 : RowData := ⟨{(-1, 0), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1)}, 4⟩
theorem entry_50_checked : entryAt 50 = entry_50 := by
  rw [entry_chunk_2 4 (by decide)]
  decide +kernel
theorem row_50 : rowAt 50 = data_50 := by
  rw [rowAt, dif_neg (by decide : ¬ 50 < 6), entry_50_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨7, 1, 5, 4⟩ (rowAt 7)] = data_50
  rw [row_6, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_50 : EntryGood 50 := by
  unfold EntryGood
  rw [entry_50_checked]
  decide +kernel
theorem good_50 : Good (rowAt 50) := by
  rw [row_50]
  unfold Good
  decide +kernel

def data_51 : RowData := ⟨{(-3, -1), (-3, 0), (-2, -1), (-2, 0), (0, -1)}, {(-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0)}, 4⟩
theorem entry_51_checked : entryAt 51 = entry_51 := by
  rw [entry_chunk_2 5 (by decide)]
  decide +kernel
theorem row_51 : rowAt 51 = data_51 := by
  rw [rowAt, dif_neg (by decide : ¬ 51 < 6), entry_51_checked]
  change forkRow [placeRow ⟨10, 2, 5, 3⟩ (rowAt 10), placeRow ⟨10, 0, 5, 4⟩ (rowAt 10), placeRow ⟨26, 2, 3, 4⟩ (rowAt 26), placeRow ⟨26, 0, 3, 3⟩ (rowAt 26)] = data_51
  rw [row_10, row_26]
  apply row_ext <;> decide +kernel
theorem entry_good_51 : EntryGood 51 := by
  unfold EntryGood
  rw [entry_51_checked]
  decide +kernel
theorem good_51 : Good (rowAt 51) := by
  rw [row_51]
  unfold Good
  decide +kernel

def data_52 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (1, -1), (2, -1)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (2, -1), (3, -1)}, 2⟩
theorem entry_52_checked : entryAt 52 = entry_52 := by
  rw [entry_chunk_2 6 (by decide)]
  decide +kernel
theorem row_52 : rowAt 52 = data_52 := by
  rw [rowAt, dif_neg (by decide : ¬ 52 < 6), entry_52_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨0, 4, 7, 3⟩ (rowAt 0)] = data_52
  rw [row_0]
  apply row_ext <;> decide +kernel
theorem entry_good_52 : EntryGood 52 := by
  unfold EntryGood
  rw [entry_52_checked]
  decide +kernel
theorem good_52 : Good (rowAt 52) := by
  rw [row_52]
  unfold Good
  decide +kernel

def data_53 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (1, 1), (1, 2), (2, -1), (3, -1)}, {(-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 1), (1, 2), (2, -1), (3, -1)}, 3⟩
theorem entry_53_checked : entryAt 53 = entry_53 := by
  rw [entry_chunk_2 7 (by decide)]
  decide +kernel
theorem row_53 : rowAt 53 = data_53 := by
  rw [rowAt, dif_neg (by decide : ¬ 53 < 6), entry_53_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨3, 1, 4, 5⟩ (rowAt 3)] = data_53
  rw [row_6, row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_53 : EntryGood 53 := by
  unfold EntryGood
  rw [entry_53_checked]
  decide +kernel
theorem good_53 : Good (rowAt 53) := by
  rw [row_53]
  unfold Good
  decide +kernel

def data_54 : RowData := ⟨{(-4, -1), (-3, -1), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)}, 3⟩
theorem entry_54_checked : entryAt 54 = entry_54 := by
  rw [entry_chunk_2 8 (by decide)]
  decide +kernel
theorem row_54 : rowAt 54 = data_54 := by
  rw [rowAt, dif_neg (by decide : ¬ 54 < 6), entry_54_checked]
  change forkRow [placeRow ⟨22, 0, 2, 3⟩ (rowAt 22), placeRow ⟨3, 6, 1, 4⟩ (rowAt 3)] = data_54
  rw [row_22, row_3]
  apply row_ext <;> decide +kernel
theorem entry_good_54 : EntryGood 54 := by
  unfold EntryGood
  rw [entry_54_checked]
  decide +kernel
theorem good_54 : Good (rowAt 54) := by
  rw [row_54]
  unfold Good
  decide +kernel

def data_55 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)}, 4⟩
theorem entry_55_checked : entryAt 55 = entry_55 := by
  rw [entry_chunk_2 9 (by decide)]
  decide +kernel
theorem row_55 : rowAt 55 = data_55 := by
  rw [rowAt, dif_neg (by decide : ¬ 55 < 6), entry_55_checked]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (rowAt 7), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_55
  rw [row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_55 : EntryGood 55 := by
  unfold EntryGood
  rw [entry_55_checked]
  decide +kernel
theorem good_55 : Good (rowAt 55) := by
  rw [row_55]
  unfold Good
  decide +kernel

def data_56 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 0)}, 4⟩
theorem entry_56_checked : entryAt 56 = entry_56 := by
  rw [entry_chunk_2 10 (by decide)]
  decide +kernel
theorem row_56 : rowAt 56 = data_56 := by
  rw [rowAt, dif_neg (by decide : ¬ 56 < 6), entry_56_checked]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (rowAt 7), placeRow ⟨7, 6, 0, 3⟩ (rowAt 7)] = data_56
  rw [row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_56 : EntryGood 56 := by
  unfold EntryGood
  rw [entry_56_checked]
  decide +kernel
theorem good_56 : Good (rowAt 56) := by
  rw [row_56]
  unfold Good
  decide +kernel

def data_57 : RowData := ⟨{(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)}, 4⟩
theorem entry_57_checked : entryAt 57 = entry_57 := by
  rw [entry_chunk_2 11 (by decide)]
  decide +kernel
theorem row_57 : rowAt 57 = data_57 := by
  rw [rowAt, dif_neg (by decide : ¬ 57 < 6), entry_57_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_57
  rw [row_0, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_57 : EntryGood 57 := by
  unfold EntryGood
  rw [entry_57_checked]
  decide +kernel
theorem good_57 : Good (rowAt 57) := by
  rw [row_57]
  unfold Good
  decide +kernel

def data_58 : RowData := ⟨{(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0)}, {(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)}, 4⟩
theorem entry_58_checked : entryAt 58 = entry_58 := by
  rw [entry_chunk_2 12 (by decide)]
  decide +kernel
theorem row_58 : rowAt 58 = data_58 := by
  rw [rowAt, dif_neg (by decide : ¬ 58 < 6), entry_58_checked]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (rowAt 0), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_58
  rw [row_0, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_58 : EntryGood 58 := by
  unfold EntryGood
  rw [entry_58_checked]
  decide +kernel
theorem good_58 : Good (rowAt 58) := by
  rw [row_58]
  unfold Good
  decide +kernel

def data_59 : RowData := ⟨{(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0)}, {(-5, 1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)}, 4⟩
theorem entry_59_checked : entryAt 59 = entry_59 := by
  rw [entry_chunk_2 13 (by decide)]
  decide +kernel
theorem row_59 : rowAt 59 = data_59 := by
  rw [rowAt, dif_neg (by decide : ¬ 59 < 6), entry_59_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨7, 4, 0, 5⟩ (rowAt 7)] = data_59
  rw [row_0, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_59 : EntryGood 59 := by
  unfold EntryGood
  rw [entry_59_checked]
  decide +kernel
theorem good_59 : Good (rowAt 59) := by
  rw [row_59]
  unfold Good
  decide +kernel

def data_60 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0), (1, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1)}, 5⟩
theorem entry_60_checked : entryAt 60 = entry_60 := by
  rw [entry_chunk_2 14 (by decide)]
  decide +kernel
theorem row_60 : rowAt 60 = data_60 := by
  rw [rowAt, dif_neg (by decide : ¬ 60 < 6), entry_60_checked]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (rowAt 6), placeRow ⟨49, 1, 6, 4⟩ (rowAt 49)] = data_60
  rw [row_6, row_49]
  apply row_ext <;> decide +kernel
theorem entry_good_60 : EntryGood 60 := by
  unfold EntryGood
  rw [entry_60_checked]
  decide +kernel
theorem good_60 : Good (rowAt 60) := by
  rw [row_60]
  unfold Good
  decide +kernel

def data_61 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (0, -1)}, {(-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0)}, 3⟩
theorem entry_61_checked : entryAt 61 = entry_61 := by
  rw [entry_chunk_2 15 (by decide)]
  decide +kernel
theorem row_61 : rowAt 61 = data_61 := by
  rw [rowAt, dif_neg (by decide : ¬ 61 < 6), entry_61_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨14, 1, 4, 5⟩ (rowAt 14)] = data_61
  rw [row_6, row_14]
  apply row_ext <;> decide +kernel
theorem entry_good_61 : EntryGood 61 := by
  unfold EntryGood
  rw [entry_61_checked]
  decide +kernel
theorem good_61 : Good (rowAt 61) := by
  rw [row_61]
  unfold Good
  decide +kernel

def data_62 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-2, 2), (-2, 3), (-1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 2), (-2, 3), (-1, 0), (0, 0)}, 4⟩
theorem entry_62_checked : entryAt 62 = entry_62 := by
  rw [entry_chunk_2 16 (by decide)]
  decide +kernel
theorem row_62 : rowAt 62 = data_62 := by
  rw [rowAt, dif_neg (by decide : ¬ 62 < 6), entry_62_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨53, 0, 1, 5⟩ (rowAt 53)] = data_62
  rw [row_6, row_53]
  apply row_ext <;> decide +kernel
theorem entry_good_62 : EntryGood 62 := by
  unfold EntryGood
  rw [entry_62_checked]
  decide +kernel
theorem good_62 : Good (rowAt 62) := by
  rw [row_62]
  unfold Good
  decide +kernel

def data_63 : RowData := ⟨{(1, -4), (1, -3), (1, -2), (1, -1)}, {(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1)}, 5⟩
theorem entry_63_checked : entryAt 63 = entry_63 := by
  rw [entry_chunk_2 17 (by decide)]
  decide +kernel
theorem row_63 : rowAt 63 = data_63 := by
  rw [rowAt, dif_neg (by decide : ¬ 63 < 6), entry_63_checked]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (rowAt 4), placeRow ⟨50, 0, 5, 4⟩ (rowAt 50)] = data_63
  rw [row_4, row_50]
  apply row_ext <;> decide +kernel
theorem entry_good_63 : EntryGood 63 := by
  unfold EntryGood
  rw [entry_63_checked]
  decide +kernel
theorem good_63 : Good (rowAt 63) := by
  rw [row_63]
  unfold Good
  decide +kernel

#check row_63
def data_64 : RowData := ⟨{(0, 1), (1, 1), (2, 1), (3, 1)}, {(-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (3, 2), (4, 1), (4, 2), (5, 2)}, 5⟩
theorem entry_64_checked : entryAt 64 = entry_64 := by
  rw [entry_chunk_2 18 (by decide)]
  decide +kernel
theorem row_64 : rowAt 64 = data_64 := by
  rw [rowAt, dif_neg (by decide : ¬ 64 < 6), entry_64_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨49, 1, 8, 5⟩ (rowAt 49)] = data_64
  rw [row_6, row_49]
  apply row_ext <;> decide +kernel
theorem entry_good_64 : EntryGood 64 := by
  unfold EntryGood
  rw [entry_64_checked]
  decide +kernel
theorem good_64 : Good (rowAt 64) := by
  rw [row_64]
  unfold Good
  decide +kernel

def data_65 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 5⟩
theorem entry_65_checked : entryAt 65 = entry_65 := by
  rw [entry_chunk_2 19 (by decide)]
  decide +kernel
theorem row_65 : rowAt 65 = data_65 := by
  rw [rowAt, dif_neg (by decide : ¬ 65 < 6), entry_65_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨49, 1, 5, 4⟩ (rowAt 49)] = data_65
  rw [row_6, row_49]
  apply row_ext <;> decide +kernel
theorem entry_good_65 : EntryGood 65 := by
  unfold EntryGood
  rw [entry_65_checked]
  decide +kernel
theorem good_65 : Good (rowAt 65) := by
  rw [row_65]
  unfold Good
  decide +kernel

def data_66 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (3, -1), (4, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (3, -1), (3, 0), (4, -1)}, 4⟩
theorem entry_66_checked : entryAt 66 = entry_66 := by
  rw [entry_chunk_3 0 (by decide)]
  decide +kernel
theorem row_66 : rowAt 66 = data_66 := by
  rw [rowAt, dif_neg (by decide : ¬ 66 < 6), entry_66_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨53, 5, 6, 4⟩ (rowAt 53)] = data_66
  rw [row_6, row_53]
  apply row_ext <;> decide +kernel
theorem entry_good_66 : EntryGood 66 := by
  unfold EntryGood
  rw [entry_66_checked]
  decide +kernel
theorem good_66 : Good (rowAt 66) := by
  rw [row_66]
  unfold Good
  decide +kernel

def data_67 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)}, 4⟩
theorem entry_67_checked : entryAt 67 = entry_67 := by
  rw [entry_chunk_3 1 (by decide)]
  decide +kernel
theorem row_67 : rowAt 67 = data_67 := by
  rw [rowAt, dif_neg (by decide : ¬ 67 < 6), entry_67_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨9, 2, 5, 4⟩ (rowAt 9)] = data_67
  rw [row_6, row_9]
  apply row_ext <;> decide +kernel
theorem entry_good_67 : EntryGood 67 := by
  unfold EntryGood
  rw [entry_67_checked]
  decide +kernel
theorem good_67 : Good (rowAt 67) := by
  rw [row_67]
  unfold Good
  decide +kernel

def data_68 : RowData := ⟨{(-3, 0), (-3, 1), (-2, 0), (-1, 0)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 5⟩
theorem entry_68_checked : entryAt 68 = entry_68 := by
  rw [entry_chunk_3 2 (by decide)]
  decide +kernel
theorem row_68 : rowAt 68 = data_68 := by
  rw [rowAt, dif_neg (by decide : ¬ 68 < 6), entry_68_checked]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (rowAt 6), placeRow ⟨44, 0, 5, 4⟩ (rowAt 44)] = data_68
  rw [row_6, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_68 : EntryGood 68 := by
  unfold EntryGood
  rw [entry_68_checked]
  decide +kernel
theorem good_68 : Good (rowAt 68) := by
  rw [row_68]
  unfold Good
  decide +kernel

def data_69 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (4, 1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 1), (2, 2), (3, 1), (4, 1)}, 4⟩
theorem entry_69_checked : entryAt 69 = entry_69 := by
  rw [entry_chunk_3 3 (by decide)]
  decide +kernel
theorem row_69 : rowAt 69 = data_69 := by
  rw [rowAt, dif_neg (by decide : ¬ 69 < 6), entry_69_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨34, 0, 6, 5⟩ (rowAt 34)] = data_69
  rw [row_6, row_34]
  apply row_ext <;> decide +kernel
theorem entry_good_69 : EntryGood 69 := by
  unfold EntryGood
  rw [entry_69_checked]
  decide +kernel
theorem good_69 : Good (rowAt 69) := by
  rw [row_69]
  unfold Good
  decide +kernel

def data_70 : RowData := ⟨{(1, -4), (1, -3), (1, -2), (1, -1), (2, -1), (4, -1)}, {(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 4⟩
theorem entry_70_checked : entryAt 70 = entry_70 := by
  rw [entry_chunk_3 4 (by decide)]
  decide +kernel
theorem row_70 : rowAt 70 = data_70 := by
  rw [rowAt, dif_neg (by decide : ¬ 70 < 6), entry_70_checked]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (rowAt 4), placeRow ⟨41, 0, 5, 4⟩ (rowAt 41)] = data_70
  rw [row_4, row_41]
  apply row_ext <;> decide +kernel
theorem entry_good_70 : EntryGood 70 := by
  unfold EntryGood
  rw [entry_70_checked]
  decide +kernel
theorem good_70 : Good (rowAt 70) := by
  rw [row_70]
  unfold Good
  decide +kernel

def data_71 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -1)}, {(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (2, -1)}, 3⟩
theorem entry_71_checked : entryAt 71 = entry_71 := by
  rw [entry_chunk_3 5 (by decide)]
  decide +kernel
theorem row_71 : rowAt 71 = data_71 := by
  rw [rowAt, dif_neg (by decide : ¬ 71 < 6), entry_71_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨23, 2, 4, 3⟩ (rowAt 23)] = data_71
  rw [row_6, row_23]
  apply row_ext <;> decide +kernel
theorem entry_good_71 : EntryGood 71 := by
  unfold EntryGood
  rw [entry_71_checked]
  decide +kernel
theorem good_71 : Good (rowAt 71) := by
  rw [row_71]
  unfold Good
  decide +kernel

def data_72 : RowData := ⟨{(-2, 1), (-1, 1), (-1, 2), (-1, 3), (0, 1), (1, 1)}, {(-3, 1), (-2, 1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0)}, 4⟩
theorem entry_72_checked : entryAt 72 = entry_72 := by
  rw [entry_chunk_3 6 (by decide)]
  decide +kernel
theorem row_72 : rowAt 72 = data_72 := by
  rw [rowAt, dif_neg (by decide : ¬ 72 < 6), entry_72_checked]
  change forkRow [placeRow ⟨0, 5, 3, 8⟩ (rowAt 0), placeRow ⟨8, 6, 5, 4⟩ (rowAt 8)] = data_72
  rw [row_0, row_8]
  apply row_ext <;> decide +kernel
theorem entry_good_72 : EntryGood 72 := by
  unfold EntryGood
  rw [entry_72_checked]
  decide +kernel
theorem good_72 : Good (rowAt 72) := by
  rw [row_72]
  unfold Good
  decide +kernel

def data_73 : RowData := ⟨{(-1, 1), (0, -3), (0, -2), (0, -1)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2)}, 5⟩
theorem entry_73_checked : entryAt 73 = entry_73 := by
  rw [entry_chunk_3 7 (by decide)]
  decide +kernel
theorem row_73 : rowAt 73 = data_73 := by
  rw [rowAt, dif_neg (by decide : ¬ 73 < 6), entry_73_checked]
  change forkRow [placeRow ⟨4, 3, 3, 4⟩ (rowAt 4), placeRow ⟨50, 0, 4, 5⟩ (rowAt 50)] = data_73
  rw [row_4, row_50]
  apply row_ext <;> decide +kernel
theorem entry_good_73 : EntryGood 73 := by
  unfold EntryGood
  rw [entry_73_checked]
  decide +kernel
theorem good_73 : Good (rowAt 73) := by
  rw [row_73]
  unfold Good
  decide +kernel

def data_74 : RowData := ⟨{(-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2), (2, -2)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (2, -2)}, 4⟩
theorem entry_74_checked : entryAt 74 = entry_74 := by
  rw [entry_chunk_3 8 (by decide)]
  decide +kernel
theorem row_74 : rowAt 74 = data_74 := by
  rw [rowAt, dif_neg (by decide : ¬ 74 < 6), entry_74_checked]
  change forkRow [placeRow ⟨2, 7, 4, 3⟩ (rowAt 2), placeRow ⟨53, 0, 3, 3⟩ (rowAt 53)] = data_74
  rw [row_2, row_53]
  apply row_ext <;> decide +kernel
theorem entry_good_74 : EntryGood 74 := by
  unfold EntryGood
  rw [entry_74_checked]
  decide +kernel
theorem good_74 : Good (rowAt 74) := by
  rw [row_74]
  unfold Good
  decide +kernel

def data_75 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, -1), (1, 0), (2, -1)}, {(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 4⟩
theorem entry_75_checked : entryAt 75 = entry_75 := by
  rw [entry_chunk_3 9 (by decide)]
  decide +kernel
theorem row_75 : rowAt 75 = data_75 := by
  rw [rowAt, dif_neg (by decide : ¬ 75 < 6), entry_75_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨9, 0, 7, 3⟩ (rowAt 9)] = data_75
  rw [row_0, row_9]
  apply row_ext <;> decide +kernel
theorem entry_good_75 : EntryGood 75 := by
  unfold EntryGood
  rw [entry_75_checked]
  decide +kernel
theorem good_75 : Good (rowAt 75) := by
  rw [row_75]
  unfold Good
  decide +kernel

def data_76 : RowData := ⟨{(-1, 0), (0, -1), (1, 0), (1, 1), (1, 2), (2, 1)}, {(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (3, 1), (4, 1)}, 3⟩
theorem entry_76_checked : entryAt 76 = entry_76 := by
  rw [entry_chunk_3 10 (by decide)]
  decide +kernel
theorem row_76 : rowAt 76 = data_76 := by
  rw [rowAt, dif_neg (by decide : ¬ 76 < 6), entry_76_checked]
  change forkRow [placeRow ⟨0, 7, 5, 7⟩ (rowAt 0), placeRow ⟨14, 0, 7, 5⟩ (rowAt 14)] = data_76
  rw [row_0, row_14]
  apply row_ext <;> decide +kernel
theorem entry_good_76 : EntryGood 76 := by
  unfold EntryGood
  rw [entry_76_checked]
  decide +kernel
theorem good_76 : Good (rowAt 76) := by
  rw [row_76]
  unfold Good
  decide +kernel

def data_77 : RowData := ⟨{(-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1)}, {(-3, -1), (-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, 0), (2, 0)}, 3⟩
theorem entry_77_checked : entryAt 77 = entry_77 := by
  rw [entry_chunk_3 11 (by decide)]
  decide +kernel
theorem row_77 : rowAt 77 = data_77 := by
  rw [rowAt, dif_neg (by decide : ¬ 77 < 6), entry_77_checked]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (rowAt 0), placeRow ⟨12, 0, 5, 4⟩ (rowAt 12)] = data_77
  rw [row_0, row_12]
  apply row_ext <;> decide +kernel
theorem entry_good_77 : EntryGood 77 := by
  unfold EntryGood
  rw [entry_77_checked]
  decide +kernel
theorem good_77 : Good (rowAt 77) := by
  rw [row_77]
  unfold Good
  decide +kernel

def data_78 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, -1), (2, -1), (3, -1)}, {(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 3⟩
theorem entry_78_checked : entryAt 78 = entry_78 := by
  rw [entry_chunk_3 12 (by decide)]
  decide +kernel
theorem row_78 : rowAt 78 = data_78 := by
  rw [rowAt, dif_neg (by decide : ¬ 78 < 6), entry_78_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨52, 0, 5, 4⟩ (rowAt 52)] = data_78
  rw [row_6, row_52]
  apply row_ext <;> decide +kernel
theorem entry_good_78 : EntryGood 78 := by
  unfold EntryGood
  rw [entry_78_checked]
  decide +kernel
theorem good_78 : Good (rowAt 78) := by
  rw [row_78]
  unfold Good
  decide +kernel

def data_79 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, 0), (2, -1), (2, 0)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1)}, 4⟩
theorem entry_79_checked : entryAt 79 = entry_79 := by
  rw [entry_chunk_3 13 (by decide)]
  decide +kernel
theorem row_79 : rowAt 79 = data_79 := by
  rw [rowAt, dif_neg (by decide : ¬ 79 < 6), entry_79_checked]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (rowAt 6), placeRow ⟨48, 0, 3, 4⟩ (rowAt 48)] = data_79
  rw [row_6, row_48]
  apply row_ext <;> decide +kernel
theorem entry_good_79 : EntryGood 79 := by
  unfold EntryGood
  rw [entry_79_checked]
  decide +kernel
theorem good_79 : Good (rowAt 79) := by
  rw [row_79]
  unfold Good
  decide +kernel

def data_80 : RowData := ⟨{(-2, -1), (-1, -1), (-1, 0), (1, -1), (1, 0), (1, 1)}, {(-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)}, 4⟩
theorem entry_80_checked : entryAt 80 = entry_80 := by
  rw [entry_chunk_3 14 (by decide)]
  decide +kernel
theorem row_80 : rowAt 80 = data_80 := by
  rw [rowAt, dif_neg (by decide : ¬ 80 < 6), entry_80_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨13, 4, 2, 4⟩ (rowAt 13)] = data_80
  rw [row_0, row_13]
  apply row_ext <;> decide +kernel
theorem entry_good_80 : EntryGood 80 := by
  unfold EntryGood
  rw [entry_80_checked]
  decide +kernel
theorem good_80 : Good (rowAt 80) := by
  rw [row_80]
  unfold Good
  decide +kernel

def data_81 : RowData := ⟨{(1, -4), (1, -3), (1, -2), (1, -1), (3, -1), (4, -1)}, {(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 4⟩
theorem entry_81_checked : entryAt 81 = entry_81 := by
  rw [entry_chunk_3 15 (by decide)]
  decide +kernel
theorem row_81 : rowAt 81 = data_81 := by
  rw [rowAt, dif_neg (by decide : ¬ 81 < 6), entry_81_checked]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (rowAt 4), placeRow ⟨43, 0, 5, 4⟩ (rowAt 43)] = data_81
  rw [row_4, row_43]
  apply row_ext <;> decide +kernel
theorem entry_good_81 : EntryGood 81 := by
  unfold EntryGood
  rw [entry_81_checked]
  decide +kernel
theorem good_81 : Good (rowAt 81) := by
  rw [row_81]
  unfold Good
  decide +kernel

def data_82 : RowData := ⟨{(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0)}, 4⟩
theorem entry_82_checked : entryAt 82 = entry_82 := by
  rw [entry_chunk_3 16 (by decide)]
  decide +kernel
theorem row_82 : rowAt 82 = data_82 := by
  rw [rowAt, dif_neg (by decide : ¬ 82 < 6), entry_82_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨36, 0, 1, 3⟩ (rowAt 36)] = data_82
  rw [row_6, row_36]
  apply row_ext <;> decide +kernel
theorem entry_good_82 : EntryGood 82 := by
  unfold EntryGood
  rw [entry_82_checked]
  decide +kernel
theorem good_82 : Good (rowAt 82) := by
  rw [row_82]
  unfold Good
  decide +kernel

def data_83 : RowData := ⟨{(0, -1), (1, -1), (1, 0), (1, 1), (1, 2)}, {(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (3, -1), (4, -1)}, 5⟩
theorem entry_83_checked : entryAt 83 = entry_83 := by
  rw [entry_chunk_3 17 (by decide)]
  decide +kernel
theorem row_83 : rowAt 83 = data_83 := by
  rw [rowAt, dif_neg (by decide : ¬ 83 < 6), entry_83_checked]
  change forkRow [placeRow ⟨0, 7, 5, 7⟩ (rowAt 0), placeRow ⟨67, 2, 6, 3⟩ (rowAt 67)] = data_83
  rw [row_0, row_67]
  apply row_ext <;> decide +kernel
theorem entry_good_83 : EntryGood 83 := by
  unfold EntryGood
  rw [entry_83_checked]
  decide +kernel
theorem good_83 : Good (rowAt 83) := by
  rw [row_83]
  unfold Good
  decide +kernel

def data_84 : RowData := ⟨{(0, -1), (1, -3), (1, -2), (1, -1), (1, 0)}, {(-1, -1), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (3, 0), (4, 0)}, 5⟩
theorem entry_84_checked : entryAt 84 = entry_84 := by
  rw [entry_chunk_3 18 (by decide)]
  decide +kernel
theorem row_84 : rowAt 84 = data_84 := by
  rw [rowAt, dif_neg (by decide : ¬ 84 < 6), entry_84_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨67, 0, 6, 4⟩ (rowAt 67)] = data_84
  rw [row_6, row_67]
  apply row_ext <;> decide +kernel
theorem entry_good_84 : EntryGood 84 := by
  unfold EntryGood
  rw [entry_84_checked]
  decide +kernel
theorem good_84 : Good (rowAt 84) := by
  rw [row_84]
  unfold Good
  decide +kernel

def data_85 : RowData := ⟨{(-2, -1), (-1, -1), (-1, 0), (0, -1), (1, -1)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1)}, 4⟩
theorem entry_85_checked : entryAt 85 = entry_85 := by
  rw [entry_chunk_3 19 (by decide)]
  decide +kernel
theorem row_85 : rowAt 85 = data_85 := by
  rw [rowAt, dif_neg (by decide : ¬ 85 < 6), entry_85_checked]
  change forkRow [placeRow ⟨9, 0, 6, 3⟩ (rowAt 9), placeRow ⟨8, 4, 5, 4⟩ (rowAt 8)] = data_85
  rw [row_9, row_8]
  apply row_ext <;> decide +kernel
theorem entry_good_85 : EntryGood 85 := by
  unfold EntryGood
  rw [entry_85_checked]
  decide +kernel
theorem good_85 : Good (rowAt 85) := by
  rw [row_85]
  unfold Good
  decide +kernel

def data_86 : RowData := ⟨{(-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0)}, {(-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)}, 5⟩
theorem entry_86_checked : entryAt 86 = entry_86 := by
  rw [entry_chunk_4 0 (by decide)]
  decide +kernel
theorem row_86 : rowAt 86 = data_86 := by
  rw [rowAt, dif_neg (by decide : ¬ 86 < 6), entry_86_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨67, 3, 1, 5⟩ (rowAt 67)] = data_86
  rw [row_0, row_67]
  apply row_ext <;> decide +kernel
theorem entry_good_86 : EntryGood 86 := by
  unfold EntryGood
  rw [entry_86_checked]
  decide +kernel
theorem good_86 : Good (rowAt 86) := by
  rw [row_86]
  unfold Good
  decide +kernel

def data_87 : RowData := ⟨{(-2, 0), (-1, 0), (-1, 1), (-1, 2), (0, -1)}, {(-3, 0), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1)}, 4⟩
theorem entry_87_checked : entryAt 87 = entry_87 := by
  rw [entry_chunk_4 1 (by decide)]
  decide +kernel
theorem row_87 : rowAt 87 = data_87 := by
  rw [rowAt, dif_neg (by decide : ¬ 87 < 6), entry_87_checked]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (rowAt 0), placeRow ⟨24, 2, 5, 3⟩ (rowAt 24)] = data_87
  rw [row_0, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_87 : EntryGood 87 := by
  unfold EntryGood
  rw [entry_87_checked]
  decide +kernel
theorem good_87 : Good (rowAt 87) := by
  rw [row_87]
  unfold Good
  decide +kernel

def data_88 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 0)}, {(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)}, 5⟩
theorem entry_88_checked : entryAt 88 = entry_88 := by
  rw [entry_chunk_4 2 (by decide)]
  decide +kernel
theorem row_88 : rowAt 88 = data_88 := by
  rw [rowAt, dif_neg (by decide : ¬ 88 < 6), entry_88_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨67, 3, 2, 5⟩ (rowAt 67)] = data_88
  rw [row_0, row_67]
  apply row_ext <;> decide +kernel
theorem entry_good_88 : EntryGood 88 := by
  unfold EntryGood
  rw [entry_88_checked]
  decide +kernel
theorem good_88 : Good (rowAt 88) := by
  rw [row_88]
  unfold Good
  decide +kernel

def data_89 : RowData := ⟨{(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -4), (-1, -3), (-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)}, 4⟩
theorem entry_89_checked : entryAt 89 = entry_89 := by
  rw [entry_chunk_4 3 (by decide)]
  decide +kernel
theorem row_89 : rowAt 89 = data_89 := by
  rw [rowAt, dif_neg (by decide : ¬ 89 < 6), entry_89_checked]
  change forkRow [placeRow ⟨8, 3, 3, 1⟩ (rowAt 8), placeRow ⟨7, 1, 5, 4⟩ (rowAt 7)] = data_89
  rw [row_8, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_89 : EntryGood 89 := by
  unfold EntryGood
  rw [entry_89_checked]
  decide +kernel
theorem good_89 : Good (rowAt 89) := by
  rw [row_89]
  unfold Good
  decide +kernel

def data_90 : RowData := ⟨{(-3, -1), (-2, -1), (-1, 0)}, {(-5, -1), (-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)}, 4⟩
theorem entry_90_checked : entryAt 90 = entry_90 := by
  rw [entry_chunk_4 4 (by decide)]
  decide +kernel
theorem row_90 : rowAt 90 = data_90 := by
  rw [rowAt, dif_neg (by decide : ¬ 90 < 6), entry_90_checked]
  change forkRow [placeRow ⟨31, 0, 3, 3⟩ (rowAt 31), placeRow ⟨54, 6, 0, 3⟩ (rowAt 54), placeRow ⟨54, 0, 5, 4⟩ (rowAt 54), placeRow ⟨31, 6, 2, 4⟩ (rowAt 31)] = data_90
  rw [row_31, row_54]
  apply row_ext <;> decide +kernel
theorem entry_good_90 : EntryGood 90 := by
  unfold EntryGood
  rw [entry_90_checked]
  decide +kernel
theorem good_90 : Good (rowAt 90) := by
  rw [row_90]
  unfold Good
  decide +kernel

def data_91 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (4, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (4, -1)}, 5⟩
theorem entry_91_checked : entryAt 91 = entry_91 := by
  rw [entry_chunk_4 5 (by decide)]
  decide +kernel
theorem row_91 : rowAt 91 = data_91 := by
  rw [rowAt, dif_neg (by decide : ¬ 91 < 6), entry_91_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨74, 5, 7, 3⟩ (rowAt 74)] = data_91
  rw [row_6, row_74]
  apply row_ext <;> decide +kernel
theorem entry_good_91 : EntryGood 91 := by
  unfold EntryGood
  rw [entry_91_checked]
  decide +kernel
theorem good_91 : Good (rowAt 91) := by
  rw [row_91]
  unfold Good
  decide +kernel

def data_92 : RowData := ⟨{(-3, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0)}, 4⟩
theorem entry_92_checked : entryAt 92 = entry_92 := by
  rw [entry_chunk_4 6 (by decide)]
  decide +kernel
theorem row_92 : rowAt 92 = data_92 := by
  rw [rowAt, dif_neg (by decide : ¬ 92 < 6), entry_92_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨33, 0, 2, 3⟩ (rowAt 33)] = data_92
  rw [row_6, row_33]
  apply row_ext <;> decide +kernel
theorem entry_good_92 : EntryGood 92 := by
  unfold EntryGood
  rw [entry_92_checked]
  decide +kernel
theorem good_92 : Good (rowAt 92) := by
  rw [row_92]
  unfold Good
  decide +kernel

def data_93 : RowData := ⟨{(1, -4), (1, -3), (1, -2), (1, -1), (2, 0), (3, -1), (3, 0)}, {(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (4, -1)}, 4⟩
theorem entry_93_checked : entryAt 93 = entry_93 := by
  rw [entry_chunk_4 7 (by decide)]
  decide +kernel
theorem row_93 : rowAt 93 = data_93 := by
  rw [rowAt, dif_neg (by decide : ¬ 93 < 6), entry_93_checked]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (rowAt 4), placeRow ⟨47, 0, 5, 4⟩ (rowAt 47)] = data_93
  rw [row_4, row_47]
  apply row_ext <;> decide +kernel
theorem entry_good_93 : EntryGood 93 := by
  unfold EntryGood
  rw [entry_93_checked]
  decide +kernel
theorem good_93 : Good (rowAt 93) := by
  rw [row_93]
  unfold Good
  decide +kernel

def data_94 : RowData := ⟨{(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1)}, {(-2, -2), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1)}, 4⟩
theorem entry_94_checked : entryAt 94 = entry_94 := by
  rw [entry_chunk_4 8 (by decide)]
  decide +kernel
theorem row_94 : rowAt 94 = data_94 := by
  rw [rowAt, dif_neg (by decide : ¬ 94 < 6), entry_94_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨27, 3, 3, 6⟩ (rowAt 27)] = data_94
  rw [row_6, row_27]
  apply row_ext <;> decide +kernel
theorem entry_good_94 : EntryGood 94 := by
  unfold EntryGood
  rw [entry_94_checked]
  decide +kernel
theorem good_94 : Good (rowAt 94) := by
  rw [row_94]
  unfold Good
  decide +kernel

def data_95 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (2, 0)}, {(-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, 0), (2, 0)}, 4⟩
theorem entry_95_checked : entryAt 95 = entry_95 := by
  rw [entry_chunk_4 9 (by decide)]
  decide +kernel
theorem row_95 : rowAt 95 = data_95 := by
  rw [rowAt, dif_neg (by decide : ¬ 95 < 6), entry_95_checked]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (rowAt 0), placeRow ⟨29, 0, 2, 5⟩ (rowAt 29)] = data_95
  rw [row_0, row_29]
  apply row_ext <;> decide +kernel
theorem entry_good_95 : EntryGood 95 := by
  unfold EntryGood
  rw [entry_95_checked]
  decide +kernel
theorem good_95 : Good (rowAt 95) := by
  rw [row_95]
  unfold Good
  decide +kernel

#check row_95
def data_96 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, 0), (3, 0)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0)}, 5⟩
theorem entry_96_checked : entryAt 96 = entry_96 := by
  rw [entry_chunk_4 10 (by decide)]
  decide +kernel
theorem row_96 : rowAt 96 = data_96 := by
  rw [rowAt, dif_neg (by decide : ¬ 96 < 6), entry_96_checked]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (rowAt 6), placeRow ⟨70, 0, 3, 5⟩ (rowAt 70)] = data_96
  rw [row_6, row_70]
  apply row_ext <;> decide +kernel
theorem entry_good_96 : EntryGood 96 := by
  unfold EntryGood
  rw [entry_96_checked]
  decide +kernel
theorem good_96 : Good (rowAt 96) := by
  rw [row_96]
  unfold Good
  decide +kernel

def data_97 : RowData := ⟨{(-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 5⟩
theorem entry_97_checked : entryAt 97 = entry_97 := by
  rw [entry_chunk_4 11 (by decide)]
  decide +kernel
theorem row_97 : rowAt 97 = data_97 := by
  rw [rowAt, dif_neg (by decide : ¬ 97 < 6), entry_97_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨44, 0, 5, 4⟩ (rowAt 44)] = data_97
  rw [row_6, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_97 : EntryGood 97 := by
  unfold EntryGood
  rw [entry_97_checked]
  decide +kernel
theorem good_97 : Good (rowAt 97) := by
  rw [row_97]
  unfold Good
  decide +kernel

def data_98 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (1, 0), (2, 0)}, {(-2, -1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1)}, 5⟩
theorem entry_98_checked : entryAt 98 = entry_98 := by
  rw [entry_chunk_4 12 (by decide)]
  decide +kernel
theorem row_98 : rowAt 98 = data_98 := by
  rw [rowAt, dif_neg (by decide : ¬ 98 < 6), entry_98_checked]
  change forkRow [placeRow ⟨6, 6, 2, 3⟩ (rowAt 6), placeRow ⟨44, 0, 7, 4⟩ (rowAt 44)] = data_98
  rw [row_6, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_98 : EntryGood 98 := by
  unfold EntryGood
  rw [entry_98_checked]
  decide +kernel
theorem good_98 : Good (rowAt 98) := by
  rw [row_98]
  unfold Good
  decide +kernel

def data_99 : RowData := ⟨{(-2, -1), (-1, -4), (-1, -3), (-1, -1), (0, -1)}, {(-3, -1), (-2, -1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -1), (0, 0), (1, -1), (1, 0), (2, 0), (3, 0)}, 4⟩
theorem entry_99_checked : entryAt 99 = entry_99 := by
  rw [entry_chunk_4 13 (by decide)]
  decide +kernel
theorem row_99 : rowAt 99 = data_99 := by
  rw [rowAt, dif_neg (by decide : ¬ 99 < 6), entry_99_checked]
  change forkRow [placeRow ⟨2, 1, 3, 2⟩ (rowAt 2), placeRow ⟨24, 0, 5, 4⟩ (rowAt 24)] = data_99
  rw [row_2, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_99 : EntryGood 99 := by
  unfold EntryGood
  rw [entry_99_checked]
  decide +kernel
theorem good_99 : Good (rowAt 99) := by
  rw [row_99]
  unfold Good
  decide +kernel

def data_100 : RowData := ⟨{(-3, -1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (0, -1)}, {(-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0)}, 4⟩
theorem entry_100_checked : entryAt 100 = entry_100 := by
  rw [entry_chunk_4 14 (by decide)]
  decide +kernel
theorem row_100 : rowAt 100 = data_100 := by
  rw [rowAt, dif_neg (by decide : ¬ 100 < 6), entry_100_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨48, 0, 1, 4⟩ (rowAt 48)] = data_100
  rw [row_0, row_48]
  apply row_ext <;> decide +kernel
theorem entry_good_100 : EntryGood 100 := by
  unfold EntryGood
  rw [entry_100_checked]
  decide +kernel
theorem good_100 : Good (rowAt 100) := by
  rw [row_100]
  unfold Good
  decide +kernel

def data_101 : RowData := ⟨{(-2, -1), (-1, -2), (-1, -1), (0, -1), (0, 1)}, {(-3, -1), (-2, -1), (-1, -2), (-1, -1), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (2, 0), (3, 0)}, 4⟩
theorem entry_101_checked : entryAt 101 = entry_101 := by
  rw [entry_chunk_4 15 (by decide)]
  decide +kernel
theorem row_101 : rowAt 101 = data_101 := by
  rw [rowAt, dif_neg (by decide : ¬ 101 < 6), entry_101_checked]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (rowAt 0), placeRow ⟨24, 0, 5, 4⟩ (rowAt 24)] = data_101
  rw [row_0, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_101 : EntryGood 101 := by
  unfold EntryGood
  rw [entry_101_checked]
  decide +kernel
theorem good_101 : Good (rowAt 101) := by
  rw [row_101]
  unfold Good
  decide +kernel

def data_102 : RowData := ⟨{(-1, 0), (1, -3), (1, -2), (1, -1), (1, 0)}, {(-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 4⟩
theorem entry_102_checked : entryAt 102 = entry_102 := by
  rw [entry_chunk_4 16 (by decide)]
  decide +kernel
theorem row_102 : rowAt 102 = data_102 := by
  rw [rowAt, dif_neg (by decide : ¬ 102 < 6), entry_102_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨25, 2, 6, 3⟩ (rowAt 25)] = data_102
  rw [row_6, row_25]
  apply row_ext <;> decide +kernel
theorem entry_good_102 : EntryGood 102 := by
  unfold EntryGood
  rw [entry_102_checked]
  decide +kernel
theorem good_102 : Good (rowAt 102) := by
  rw [row_102]
  unfold Good
  decide +kernel

def data_103 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (3, -1)}, {(-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (4, -1)}, 4⟩
theorem entry_103_checked : entryAt 103 = entry_103 := by
  rw [entry_chunk_4 17 (by decide)]
  decide +kernel
theorem row_103 : rowAt 103 = data_103 := by
  rw [rowAt, dif_neg (by decide : ¬ 103 < 6), entry_103_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨71, 0, 6, 4⟩ (rowAt 71)] = data_103
  rw [row_6, row_71]
  apply row_ext <;> decide +kernel
theorem entry_good_103 : EntryGood 103 := by
  unfold EntryGood
  rw [entry_103_checked]
  decide +kernel
theorem good_103 : Good (rowAt 103) := by
  rw [row_103]
  unfold Good
  decide +kernel

def data_104 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (0, -1), (1, -1)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1)}, 5⟩
theorem entry_104_checked : entryAt 104 = entry_104 := by
  rw [entry_chunk_4 18 (by decide)]
  decide +kernel
theorem row_104 : rowAt 104 = data_104 := by
  rw [rowAt, dif_neg (by decide : ¬ 104 < 6), entry_104_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨75, 0, 3, 4⟩ (rowAt 75)] = data_104
  rw [row_6, row_75]
  apply row_ext <;> decide +kernel
theorem entry_good_104 : EntryGood 104 := by
  unfold EntryGood
  rw [entry_104_checked]
  decide +kernel
theorem good_104 : Good (rowAt 104) := by
  rw [row_104]
  unfold Good
  decide +kernel

def data_105 : RowData := ⟨{(-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3)}, {(-3, 0), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (1, 1), (2, 1)}, 4⟩
theorem entry_105_checked : entryAt 105 = entry_105 := by
  rw [entry_chunk_4 19 (by decide)]
  decide +kernel
theorem row_105 : rowAt 105 = data_105 := by
  rw [rowAt, dif_neg (by decide : ¬ 105 < 6), entry_105_checked]
  change forkRow [placeRow ⟨6, 5, 4, 3⟩ (rowAt 6), placeRow ⟨77, 0, 4, 5⟩ (rowAt 77)] = data_105
  rw [row_6, row_77]
  apply row_ext <;> decide +kernel
theorem entry_good_105 : EntryGood 105 := by
  unfold EntryGood
  rw [entry_105_checked]
  decide +kernel
theorem good_105 : Good (rowAt 105) := by
  rw [row_105]
  unfold Good
  decide +kernel

def data_106 : RowData := ⟨{(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)}, 4⟩
theorem entry_106_checked : entryAt 106 = entry_106 := by
  rw [entry_chunk_5 0 (by decide)]
  decide +kernel
theorem row_106 : rowAt 106 = data_106 := by
  rw [rowAt, dif_neg (by decide : ¬ 106 < 6), entry_106_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨36, 6, 5, 4⟩ (rowAt 36)] = data_106
  rw [row_6, row_36]
  apply row_ext <;> decide +kernel
theorem entry_good_106 : EntryGood 106 := by
  unfold EntryGood
  rw [entry_106_checked]
  decide +kernel
theorem good_106 : Good (rowAt 106) := by
  rw [row_106]
  unfold Good
  decide +kernel

def data_107 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 6⟩
theorem entry_107_checked : entryAt 107 = entry_107 := by
  rw [entry_chunk_5 1 (by decide)]
  decide +kernel
theorem row_107 : rowAt 107 = data_107 := by
  rw [rowAt, dif_neg (by decide : ¬ 107 < 6), entry_107_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63)] = data_107
  rw [row_6, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_107 : EntryGood 107 := by
  unfold EntryGood
  rw [entry_107_checked]
  decide +kernel
theorem good_107 : Good (rowAt 107) := by
  rw [row_107]
  unfold Good
  decide +kernel

def data_108 : RowData := ⟨{(-4, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 6⟩
theorem entry_108_checked : entryAt 108 = entry_108 := by
  rw [entry_chunk_5 2 (by decide)]
  decide +kernel
theorem row_108 : rowAt 108 = data_108 := by
  rw [rowAt, dif_neg (by decide : ¬ 108 < 6), entry_108_checked]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (rowAt 4), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63)] = data_108
  rw [row_4, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_108 : EntryGood 108 := by
  unfold EntryGood
  rw [entry_108_checked]
  decide +kernel
theorem good_108 : Good (rowAt 108) := by
  rw [row_108]
  unfold Good
  decide +kernel

def data_109 : RowData := ⟨{(-4, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 5⟩
theorem entry_109_checked : entryAt 109 = entry_109 := by
  rw [entry_chunk_5 3 (by decide)]
  decide +kernel
theorem row_109 : rowAt 109 = data_109 := by
  rw [rowAt, dif_neg (by decide : ¬ 109 < 6), entry_109_checked]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (rowAt 4), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55)] = data_109
  rw [row_4, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_109 : EntryGood 109 := by
  unfold EntryGood
  rw [entry_109_checked]
  decide +kernel
theorem good_109 : Good (rowAt 109) := by
  rw [row_109]
  unfold Good
  decide +kernel

def data_110 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0), (1, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 6⟩
theorem entry_110_checked : entryAt 110 = entry_110 := by
  rw [entry_chunk_5 4 (by decide)]
  decide +kernel
theorem row_110 : rowAt 110 = data_110 := by
  rw [rowAt, dif_neg (by decide : ¬ 110 < 6), entry_110_checked]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (rowAt 6), placeRow ⟨63, 1, 6, 3⟩ (rowAt 63)] = data_110
  rw [row_6, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_110 : EntryGood 110 := by
  unfold EntryGood
  rw [entry_110_checked]
  decide +kernel
theorem good_110 : Good (rowAt 110) := by
  rw [row_110]
  unfold Good
  decide +kernel

def data_111 : RowData := ⟨{(1, 0), (1, 1), (1, 2), (1, 3)}, {(-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (3, 0), (4, 0)}, 6⟩
theorem entry_111_checked : entryAt 111 = entry_111 := by
  rw [entry_chunk_5 5 (by decide)]
  decide +kernel
theorem row_111 : rowAt 111 = data_111 := by
  rw [rowAt, dif_neg (by decide : ¬ 111 < 6), entry_111_checked]
  change forkRow [placeRow ⟨6, 7, 4, 3⟩ (rowAt 6), placeRow ⟨83, 0, 4, 5⟩ (rowAt 83)] = data_111
  rw [row_6, row_83]
  apply row_ext <;> decide +kernel
theorem entry_good_111 : EntryGood 111 := by
  unfold EntryGood
  rw [entry_111_checked]
  decide +kernel
theorem good_111 : Good (rowAt 111) := by
  rw [row_111]
  unfold Good
  decide +kernel

def data_112 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, 1), (2, 0), (2, 1)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0)}, 5⟩
theorem entry_112_checked : entryAt 112 = entry_112 := by
  rw [entry_chunk_5 6 (by decide)]
  decide +kernel
theorem row_112 : rowAt 112 = data_112 := by
  rw [rowAt, dif_neg (by decide : ¬ 112 < 6), entry_112_checked]
  change forkRow [placeRow ⟨4, 1, 5, 4⟩ (rowAt 4), placeRow ⟨93, 0, 3, 5⟩ (rowAt 93)] = data_112
  rw [row_4, row_93]
  apply row_ext <;> decide +kernel
theorem entry_good_112 : EntryGood 112 := by
  unfold EntryGood
  rw [entry_112_checked]
  decide +kernel
theorem good_112 : Good (rowAt 112) := by
  rw [row_112]
  unfold Good
  decide +kernel

def data_113 : RowData := ⟨{(-1, -1), (0, -1), (1, 0), (1, 1), (2, 1), (3, 0)}, {(-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1)}, 4⟩
theorem entry_113_checked : entryAt 113 = entry_113 := by
  rw [entry_chunk_5 7 (by decide)]
  decide +kernel
theorem row_113 : rowAt 113 = data_113 := by
  rw [rowAt, dif_neg (by decide : ¬ 113 < 6), entry_113_checked]
  change forkRow [placeRow ⟨1, 6, 6, 4⟩ (rowAt 1), placeRow ⟨36, 6, 7, 5⟩ (rowAt 36)] = data_113
  rw [row_1, row_36]
  apply row_ext <;> decide +kernel
theorem entry_good_113 : EntryGood 113 := by
  unfold EntryGood
  rw [entry_113_checked]
  decide +kernel
theorem good_113 : Good (rowAt 113) := by
  rw [row_113]
  unfold Good
  decide +kernel

def data_114 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 0), (1, 1)}, {(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)}, 5⟩
theorem entry_114_checked : entryAt 114 = entry_114 := by
  rw [entry_chunk_5 8 (by decide)]
  decide +kernel
theorem row_114 : rowAt 114 = data_114 := by
  rw [rowAt, dif_neg (by decide : ¬ 114 < 6), entry_114_checked]
  change forkRow [placeRow ⟨6, 0, 6, 5⟩ (rowAt 6), placeRow ⟨67, 3, 2, 5⟩ (rowAt 67)] = data_114
  rw [row_6, row_67]
  apply row_ext <;> decide +kernel
theorem entry_good_114 : EntryGood 114 := by
  unfold EntryGood
  rw [entry_114_checked]
  decide +kernel
theorem good_114 : Good (rowAt 114) := by
  rw [row_114]
  unfold Good
  decide +kernel

def data_115 : RowData := ⟨{(-1, -3), (-1, -1), (-1, 0), (1, 0), (2, -1), (2, 0)}, {(-3, 1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 0), (2, -1), (2, 0), (3, -1)}, 5⟩
theorem entry_115_checked : entryAt 115 = entry_115 := by
  rw [entry_chunk_5 9 (by decide)]
  decide +kernel
theorem row_115 : rowAt 115 = data_115 := by
  rw [rowAt, dif_neg (by decide : ¬ 115 < 6), entry_115_checked]
  change forkRow [placeRow ⟨6, 2, 7, 3⟩ (rowAt 6), placeRow ⟨70, 7, 2, 5⟩ (rowAt 70)] = data_115
  rw [row_6, row_70]
  apply row_ext <;> decide +kernel
theorem entry_good_115 : EntryGood 115 := by
  unfold EntryGood
  rw [entry_115_checked]
  decide +kernel
theorem good_115 : Good (rowAt 115) := by
  rw [row_115]
  unfold Good
  decide +kernel

def data_116 : RowData := ⟨{(-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 1)}, {(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (3, 0)}, 4⟩
theorem entry_116_checked : entryAt 116 = entry_116 := by
  rw [entry_chunk_5 10 (by decide)]
  decide +kernel
theorem row_116 : rowAt 116 = data_116 := by
  rw [rowAt, dif_neg (by decide : ¬ 116 < 6), entry_116_checked]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (rowAt 0), placeRow ⟨24, 2, 5, 4⟩ (rowAt 24)] = data_116
  rw [row_0, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_116 : EntryGood 116 := by
  unfold EntryGood
  rw [entry_116_checked]
  decide +kernel
theorem good_116 : Good (rowAt 116) := by
  rw [row_116]
  unfold Good
  decide +kernel

def data_117 : RowData := ⟨{(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -1)}, {(-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0)}, 5⟩
theorem entry_117_checked : entryAt 117 = entry_117 := by
  rw [entry_chunk_5 11 (by decide)]
  decide +kernel
theorem row_117 : rowAt 117 = data_117 := by
  rw [rowAt, dif_neg (by decide : ¬ 117 < 6), entry_117_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨100, 0, 5, 4⟩ (rowAt 100)] = data_117
  rw [row_6, row_100]
  apply row_ext <;> decide +kernel
theorem entry_good_117 : EntryGood 117 := by
  unfold EntryGood
  rw [entry_117_checked]
  decide +kernel
theorem good_117 : Good (rowAt 117) := by
  rw [row_117]
  unfold Good
  decide +kernel

def data_118 : RowData := ⟨{(-2, -1), (-1, -4), (-1, -1), (0, -3), (0, -2), (0, -1)}, {(-2, -1), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, 0), (3, 0)}, 4⟩
theorem entry_118_checked : entryAt 118 = entry_118 := by
  rw [entry_chunk_5 12 (by decide)]
  decide +kernel
theorem row_118 : rowAt 118 = data_118 := by
  rw [rowAt, dif_neg (by decide : ¬ 118 < 6), entry_118_checked]
  change forkRow [placeRow ⟨4, 7, 3, 1⟩ (rowAt 4), placeRow ⟨61, 1, 5, 4⟩ (rowAt 61)] = data_118
  rw [row_4, row_61]
  apply row_ext <;> decide +kernel
theorem entry_good_118 : EntryGood 118 := by
  unfold EntryGood
  rw [entry_118_checked]
  decide +kernel
theorem good_118 : Good (rowAt 118) := by
  rw [row_118]
  unfold Good
  decide +kernel

def data_119 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0), (1, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1)}, 5⟩
theorem entry_119_checked : entryAt 119 = entry_119 := by
  rw [entry_chunk_5 13 (by decide)]
  decide +kernel
theorem row_119 : rowAt 119 = data_119 := by
  rw [rowAt, dif_neg (by decide : ¬ 119 < 6), entry_119_checked]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (rowAt 6), placeRow ⟨55, 0, 6, 4⟩ (rowAt 55)] = data_119
  rw [row_6, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_119 : EntryGood 119 := by
  unfold EntryGood
  rw [entry_119_checked]
  decide +kernel
theorem good_119 : Good (rowAt 119) := by
  rw [row_119]
  unfold Good
  decide +kernel

def data_120 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 1)}, {(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)}, 5⟩
theorem entry_120_checked : entryAt 120 = entry_120 := by
  rw [entry_chunk_5 14 (by decide)]
  decide +kernel
theorem row_120 : rowAt 120 = data_120 := by
  rw [rowAt, dif_neg (by decide : ¬ 120 < 6), entry_120_checked]
  change forkRow [placeRow ⟨4, 0, 4, 5⟩ (rowAt 4), placeRow ⟨58, 2, 5, 4⟩ (rowAt 58)] = data_120
  rw [row_4, row_58]
  apply row_ext <;> decide +kernel
theorem entry_good_120 : EntryGood 120 := by
  unfold EntryGood
  rw [entry_120_checked]
  decide +kernel
theorem good_120 : Good (rowAt 120) := by
  rw [row_120]
  unfold Good
  decide +kernel

def data_121 : RowData := ⟨{(-1, -2), (-1, -1), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -3), (-1, -2), (-1, -1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1)}, 4⟩
theorem entry_121_checked : entryAt 121 = entry_121 := by
  rw [entry_chunk_5 15 (by decide)]
  decide +kernel
theorem row_121 : rowAt 121 = data_121 := by
  rw [rowAt, dif_neg (by decide : ¬ 121 < 6), entry_121_checked]
  change forkRow [placeRow ⟨9, 3, 4, 5⟩ (rowAt 9), placeRow ⟨7, 1, 5, 4⟩ (rowAt 7)] = data_121
  rw [row_9, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_121 : EntryGood 121 := by
  unfold EntryGood
  rw [entry_121_checked]
  decide +kernel
theorem good_121 : Good (rowAt 121) := by
  rw [row_121]
  unfold Good
  decide +kernel

def data_122 : RowData := ⟨{(0, -1), (1, 0), (2, 0), (3, 0)}, {(-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (3, 0), (4, 0)}, 5⟩
theorem entry_122_checked : entryAt 122 = entry_122 := by
  rw [entry_chunk_5 16 (by decide)]
  decide +kernel
theorem row_122 : rowAt 122 = data_122 := by
  rw [rowAt, dif_neg (by decide : ¬ 122 < 6), entry_122_checked]
  change forkRow [placeRow ⟨6, 6, 3, 3⟩ (rowAt 6), placeRow ⟨105, 1, 4, 5⟩ (rowAt 105)] = data_122
  rw [row_6, row_105]
  apply row_ext <;> decide +kernel
theorem entry_good_122 : EntryGood 122 := by
  unfold EntryGood
  rw [entry_122_checked]
  decide +kernel
theorem good_122 : Good (rowAt 122) := by
  rw [row_122]
  unfold Good
  decide +kernel

def data_123 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0), (1, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1)}, 6⟩
theorem entry_123_checked : entryAt 123 = entry_123 := by
  rw [entry_chunk_5 17 (by decide)]
  decide +kernel
theorem row_123 : rowAt 123 = data_123 := by
  rw [rowAt, dif_neg (by decide : ¬ 123 < 6), entry_123_checked]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (rowAt 6), placeRow ⟨64, 2, 2, 5⟩ (rowAt 64)] = data_123
  rw [row_6, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_123 : EntryGood 123 := by
  unfold EntryGood
  rw [entry_123_checked]
  decide +kernel
theorem good_123 : Good (rowAt 123) := by
  rw [row_123]
  unfold Good
  decide +kernel

def data_124 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -1), (2, -1)}, {(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (4, -1)}, 4⟩
theorem entry_124_checked : entryAt 124 = entry_124 := by
  rw [entry_chunk_5 18 (by decide)]
  decide +kernel
theorem row_124 : rowAt 124 = data_124 := by
  rw [rowAt, dif_neg (by decide : ¬ 124 < 6), entry_124_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨31, 2, 5, 4⟩ (rowAt 31)] = data_124
  rw [row_6, row_31]
  apply row_ext <;> decide +kernel
theorem entry_good_124 : EntryGood 124 := by
  unfold EntryGood
  rw [entry_124_checked]
  decide +kernel
theorem good_124 : Good (rowAt 124) := by
  rw [row_124]
  unfold Good
  decide +kernel

def data_125 : RowData := ⟨{(-3, -1), (-2, -1), (-2, 1), (-1, -1), (-1, 1), (1, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 1), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0)}, 4⟩
theorem entry_125_checked : entryAt 125 = entry_125 := by
  rw [entry_chunk_5 19 (by decide)]
  decide +kernel
theorem row_125 : rowAt 125 = data_125 := by
  rw [rowAt, dif_neg (by decide : ¬ 125 < 6), entry_125_checked]
  change forkRow [placeRow ⟨3, 0, 4, 3⟩ (rowAt 3), placeRow ⟨31, 2, 4, 5⟩ (rowAt 31)] = data_125
  rw [row_3, row_31]
  apply row_ext <;> decide +kernel
theorem entry_good_125 : EntryGood 125 := by
  unfold EntryGood
  rw [entry_125_checked]
  decide +kernel
theorem good_125 : Good (rowAt 125) := by
  rw [row_125]
  unfold Good
  decide +kernel

def data_126 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2)}, {(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4)}, 5⟩
theorem entry_126_checked : entryAt 126 = entry_126 := by
  rw [entry_chunk_6 0 (by decide)]
  decide +kernel
theorem row_126 : rowAt 126 = data_126 := by
  rw [rowAt, dif_neg (by decide : ¬ 126 < 6), entry_126_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨46, 1, 5, 7⟩ (rowAt 46)] = data_126
  rw [row_6, row_46]
  apply row_ext <;> decide +kernel
theorem entry_good_126 : EntryGood 126 := by
  unfold EntryGood
  rw [entry_126_checked]
  decide +kernel
theorem good_126 : Good (rowAt 126) := by
  rw [row_126]
  unfold Good
  decide +kernel

def data_127 : RowData := ⟨{(-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1)}, 5⟩
theorem entry_127_checked : entryAt 127 = entry_127 := by
  rw [entry_chunk_6 1 (by decide)]
  decide +kernel
theorem row_127 : rowAt 127 = data_127 := by
  rw [rowAt, dif_neg (by decide : ¬ 127 < 6), entry_127_checked]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (rowAt 7), placeRow ⟨44, 2, 5, 4⟩ (rowAt 44)] = data_127
  rw [row_7, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_127 : EntryGood 127 := by
  unfold EntryGood
  rw [entry_127_checked]
  decide +kernel
theorem good_127 : Good (rowAt 127) := by
  rw [row_127]
  unfold Good
  decide +kernel

#check row_127
def data_128 : RowData := ⟨{(-2, 1), (-1, 0), (-1, 1), (0, 1), (1, 1)}, {(-4, 1), (-3, 1), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2)}, 5⟩
theorem entry_128_checked : entryAt 128 = entry_128 := by
  rw [entry_chunk_6 2 (by decide)]
  decide +kernel
theorem row_128 : rowAt 128 = data_128 := by
  rw [rowAt, dif_neg (by decide : ¬ 128 < 6), entry_128_checked]
  change forkRow [placeRow ⟨9, 6, 1, 5⟩ (rowAt 9), placeRow ⟨57, 0, 6, 5⟩ (rowAt 57)] = data_128
  rw [row_9, row_57]
  apply row_ext <;> decide +kernel
theorem entry_good_128 : EntryGood 128 := by
  unfold EntryGood
  rw [entry_128_checked]
  decide +kernel
theorem good_128 : Good (rowAt 128) := by
  rw [row_128]
  unfold Good
  decide +kernel

def data_129 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (1, 0), (2, 0)}, {(-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)}, 5⟩
theorem entry_129_checked : entryAt 129 = entry_129 := by
  rw [entry_chunk_6 3 (by decide)]
  decide +kernel
theorem row_129 : rowAt 129 = data_129 := by
  rw [rowAt, dif_neg (by decide : ¬ 129 < 6), entry_129_checked]
  change forkRow [placeRow ⟨6, 4, 2, 5⟩ (rowAt 6), placeRow ⟨58, 1, 3, 6⟩ (rowAt 58)] = data_129
  rw [row_6, row_58]
  apply row_ext <;> decide +kernel
theorem entry_good_129 : EntryGood 129 := by
  unfold EntryGood
  rw [entry_129_checked]
  decide +kernel
theorem good_129 : Good (rowAt 129) := by
  rw [row_129]
  unfold Good
  decide +kernel

def data_130 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, 0)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1)}, 6⟩
theorem entry_130_checked : entryAt 130 = entry_130 := by
  rw [entry_chunk_6 4 (by decide)]
  decide +kernel
theorem row_130 : rowAt 130 = data_130 := by
  rw [rowAt, dif_neg (by decide : ¬ 130 < 6), entry_130_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨60, 0, 5, 4⟩ (rowAt 60)] = data_130
  rw [row_6, row_60]
  apply row_ext <;> decide +kernel
theorem entry_good_130 : EntryGood 130 := by
  unfold EntryGood
  rw [entry_130_checked]
  decide +kernel
theorem good_130 : Good (rowAt 130) := by
  rw [row_130]
  unfold Good
  decide +kernel

def data_131 : RowData := ⟨{(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)}, 5⟩
theorem entry_131_checked : entryAt 131 = entry_131 := by
  rw [entry_chunk_6 5 (by decide)]
  decide +kernel
theorem row_131 : rowAt 131 = data_131 := by
  rw [rowAt, dif_neg (by decide : ¬ 131 < 6), entry_131_checked]
  change forkRow [placeRow ⟨45, 3, 4, 5⟩ (rowAt 45), placeRow ⟨7, 1, 5, 4⟩ (rowAt 7)] = data_131
  rw [row_45, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_131 : EntryGood 131 := by
  unfold EntryGood
  rw [entry_131_checked]
  decide +kernel
theorem good_131 : Good (rowAt 131) := by
  rw [row_131]
  unfold Good
  decide +kernel

def data_132 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (1, 1)}, {(0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)}, 5⟩
theorem entry_132_checked : entryAt 132 = entry_132 := by
  rw [entry_chunk_6 6 (by decide)]
  decide +kernel
theorem row_132 : rowAt 132 = data_132 := by
  rw [rowAt, dif_neg (by decide : ¬ 132 < 6), entry_132_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨89, 0, 5, 6⟩ (rowAt 89)] = data_132
  rw [row_6, row_89]
  apply row_ext <;> decide +kernel
theorem entry_good_132 : EntryGood 132 := by
  unfold EntryGood
  rw [entry_132_checked]
  decide +kernel
theorem good_132 : Good (rowAt 132) := by
  rw [row_132]
  unfold Good
  decide +kernel

def data_133 : RowData := ⟨{(-2, 0), (-1, -2), (0, -2), (0, -1), (0, 1)}, {(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (3, 1)}, 5⟩
theorem entry_133_checked : entryAt 133 = entry_133 := by
  rw [entry_chunk_6 7 (by decide)]
  decide +kernel
theorem row_133 : rowAt 133 = data_133 := by
  rw [rowAt, dif_neg (by decide : ¬ 133 < 6), entry_133_checked]
  change forkRow [placeRow ⟨6, 7, 3, 1⟩ (rowAt 6), placeRow ⟨92, 0, 5, 5⟩ (rowAt 92)] = data_133
  rw [row_6, row_92]
  apply row_ext <;> decide +kernel
theorem entry_good_133 : EntryGood 133 := by
  unfold EntryGood
  rw [entry_133_checked]
  decide +kernel
theorem good_133 : Good (rowAt 133) := by
  rw [row_133]
  unfold Good
  decide +kernel

def data_134 : RowData := ⟨{(-1, -3), (-1, -1), (0, -3), (0, -2), (0, -1)}, {(-3, -1), (-2, -1), (-1, -4), (-1, -3), (-1, -1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, 0), (3, 0)}, 5⟩
theorem entry_134_checked : entryAt 134 = entry_134 := by
  rw [entry_chunk_6 8 (by decide)]
  decide +kernel
theorem row_134 : rowAt 134 = data_134 := by
  rw [rowAt, dif_neg (by decide : ¬ 134 < 6), entry_134_checked]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (rowAt 6), placeRow ⟨82, 0, 5, 4⟩ (rowAt 82)] = data_134
  rw [row_6, row_82]
  apply row_ext <;> decide +kernel
theorem entry_good_134 : EntryGood 134 := by
  unfold EntryGood
  rw [entry_134_checked]
  decide +kernel
theorem good_134 : Good (rowAt 134) := by
  rw [row_134]
  unfold Good
  decide +kernel

def data_135 : RowData := ⟨{(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-1, 0)}, {(-6, 0), (-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 5⟩
theorem entry_135_checked : entryAt 135 = entry_135 := by
  rw [entry_chunk_6 9 (by decide)]
  decide +kernel
theorem row_135 : rowAt 135 = data_135 := by
  rw [rowAt, dif_neg (by decide : ¬ 135 < 6), entry_135_checked]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (rowAt 7), placeRow ⟨75, 4, 2, 5⟩ (rowAt 75), placeRow ⟨44, 0, 5, 4⟩ (rowAt 44)] = data_135
  rw [row_7, row_75, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_135 : EntryGood 135 := by
  unfold EntryGood
  rw [entry_135_checked]
  decide +kernel
theorem good_135 : Good (rowAt 135) := by
  rw [row_135]
  unfold Good
  decide +kernel

def data_136 : RowData := ⟨{(-2, -1), (-1, 2), (0, -1), (0, 1), (0, 2)}, {(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (2, 0), (3, 0)}, 5⟩
theorem entry_136_checked : entryAt 136 = entry_136 := by
  rw [entry_chunk_6 10 (by decide)]
  decide +kernel
theorem row_136 : rowAt 136 = data_136 := by
  rw [rowAt, dif_neg (by decide : ¬ 136 < 6), entry_136_checked]
  change forkRow [placeRow ⟨6, 3, 3, 7⟩ (rowAt 6), placeRow ⟨102, 2, 3, 3⟩ (rowAt 102)] = data_136
  rw [row_6, row_102]
  apply row_ext <;> decide +kernel
theorem entry_good_136 : EntryGood 136 := by
  unfold EntryGood
  rw [entry_136_checked]
  decide +kernel
theorem good_136 : Good (rowAt 136) := by
  rw [row_136]
  unfold Good
  decide +kernel

def data_137 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (-1, -1), (2, 0)}, {(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0)}, 6⟩
theorem entry_137_checked : entryAt 137 = entry_137 := by
  rw [entry_chunk_6 11 (by decide)]
  decide +kernel
theorem row_137 : rowAt 137 = data_137 := by
  rw [rowAt, dif_neg (by decide : ¬ 137 < 6), entry_137_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨96, 0, 3, 4⟩ (rowAt 96)] = data_137
  rw [row_4, row_96]
  apply row_ext <;> decide +kernel
theorem entry_good_137 : EntryGood 137 := by
  unfold EntryGood
  rw [entry_137_checked]
  decide +kernel
theorem good_137 : Good (rowAt 137) := by
  rw [row_137]
  unfold Good
  decide +kernel

def data_138 : RowData := ⟨{(-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 2), (0, 2)}, {(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)}, 4⟩
theorem entry_138_checked : entryAt 138 = entry_138 := by
  rw [entry_chunk_6 12 (by decide)]
  decide +kernel
theorem row_138 : rowAt 138 = data_138 := by
  rw [rowAt, dif_neg (by decide : ¬ 138 < 6), entry_138_checked]
  change forkRow [placeRow ⟨27, 0, 5, 4⟩ (rowAt 27), placeRow ⟨10, 1, 4, 7⟩ (rowAt 10)] = data_138
  rw [row_27, row_10]
  apply row_ext <;> decide +kernel
theorem entry_good_138 : EntryGood 138 := by
  unfold EntryGood
  rw [entry_138_checked]
  decide +kernel
theorem good_138 : Good (rowAt 138) := by
  rw [row_138]
  unfold Good
  decide +kernel

def data_139 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 2)}, {(-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0)}, 4⟩
theorem entry_139_checked : entryAt 139 = entry_139 := by
  rw [entry_chunk_6 13 (by decide)]
  decide +kernel
theorem row_139 : rowAt 139 = data_139 := by
  rw [rowAt, dif_neg (by decide : ¬ 139 < 6), entry_139_checked]
  change forkRow [placeRow ⟨28, 1, 4, 5⟩ (rowAt 28), placeRow ⟨27, 0, 5, 4⟩ (rowAt 27)] = data_139
  rw [row_28, row_27]
  apply row_ext <;> decide +kernel
theorem entry_good_139 : EntryGood 139 := by
  unfold EntryGood
  rw [entry_139_checked]
  decide +kernel
theorem good_139 : Good (rowAt 139) := by
  rw [row_139]
  unfold Good
  decide +kernel

def data_140 : RowData := ⟨{(-1, -1), (-1, 1), (0, -1), (0, 1), (0, 2)}, {(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 2), (3, 2)}, 5⟩
theorem entry_140_checked : entryAt 140 = entry_140 := by
  rw [entry_chunk_6 14 (by decide)]
  decide +kernel
theorem row_140 : rowAt 140 = data_140 := by
  rw [rowAt, dif_neg (by decide : ¬ 140 < 6), entry_140_checked]
  change forkRow [placeRow ⟨6, 7, 3, 2⟩ (rowAt 6), placeRow ⟨82, 0, 5, 6⟩ (rowAt 82)] = data_140
  rw [row_6, row_82]
  apply row_ext <;> decide +kernel
theorem entry_good_140 : EntryGood 140 := by
  unfold EntryGood
  rw [entry_140_checked]
  decide +kernel
theorem good_140 : Good (rowAt 140) := by
  rw [row_140]
  unfold Good
  decide +kernel

def data_141 : RowData := ⟨{(-5, 0), (-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-6, 0), (-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)}, 4⟩
theorem entry_141_checked : entryAt 141 = entry_141 := by
  rw [entry_chunk_6 15 (by decide)]
  decide +kernel
theorem row_141 : rowAt 141 = data_141 := by
  rw [rowAt, dif_neg (by decide : ¬ 141 < 6), entry_141_checked]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (rowAt 7), placeRow ⟨78, 2, 1, 3⟩ (rowAt 78)] = data_141
  rw [row_7, row_78]
  apply row_ext <;> decide +kernel
theorem entry_good_141 : EntryGood 141 := by
  unfold EntryGood
  rw [entry_141_checked]
  decide +kernel
theorem good_141 : Good (rowAt 141) := by
  rw [row_141]
  unfold Good
  decide +kernel

def data_142 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0), (-1, 1), (-1, 2)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)}, 5⟩
theorem entry_142_checked : entryAt 142 = entry_142 := by
  rw [entry_chunk_6 16 (by decide)]
  decide +kernel
theorem row_142 : rowAt 142 = data_142 := by
  rw [rowAt, dif_neg (by decide : ¬ 142 < 6), entry_142_checked]
  change forkRow [placeRow ⟨72, 4, 2, 3⟩ (rowAt 72), placeRow ⟨32, 1, 4, 3⟩ (rowAt 32), placeRow ⟨55, 2, 5, 4⟩ (rowAt 55)] = data_142
  rw [row_72, row_32, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_142 : EntryGood 142 := by
  unfold EntryGood
  rw [entry_142_checked]
  decide +kernel
theorem good_142 : Good (rowAt 142) := by
  rw [row_142]
  unfold Good
  decide +kernel

def data_143 : RowData := ⟨{(0, 1), (1, 1), (2, 1), (3, 1)}, {(-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)}, 7⟩
theorem entry_143_checked : entryAt 143 = entry_143 := by
  rw [entry_chunk_6 17 (by decide)]
  decide +kernel
theorem row_143 : rowAt 143 = data_143 := by
  rw [rowAt, dif_neg (by decide : ¬ 143 < 6), entry_143_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨108, 0, 8, 5⟩ (rowAt 108)] = data_143
  rw [row_6, row_108]
  apply row_ext <;> decide +kernel
theorem entry_good_143 : EntryGood 143 := by
  unfold EntryGood
  rw [entry_143_checked]
  decide +kernel
theorem good_143 : Good (rowAt 143) := by
  rw [row_143]
  unfold Good
  decide +kernel

def data_144 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-6, 0), (-5, 0), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 6⟩
theorem entry_144_checked : entryAt 144 = entry_144 := by
  rw [entry_chunk_6 18 (by decide)]
  decide +kernel
theorem row_144 : rowAt 144 = data_144 := by
  rw [rowAt, dif_neg (by decide : ¬ 144 < 6), entry_144_checked]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (rowAt 7), placeRow ⟨104, 4, 1, 5⟩ (rowAt 104), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55)] = data_144
  rw [row_7, row_104, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_144 : EntryGood 144 := by
  unfold EntryGood
  rw [entry_144_checked]
  decide +kernel
theorem good_144 : Good (rowAt 144) := by
  rw [row_144]
  unfold Good
  decide +kernel

def data_145 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3), (1, -2), (3, -1)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1)}, 6⟩
theorem entry_145_checked : entryAt 145 = entry_145 := by
  rw [entry_chunk_6 19 (by decide)]
  decide +kernel
theorem row_145 : rowAt 145 = data_145 := by
  rw [rowAt, dif_neg (by decide : ¬ 145 < 6), entry_145_checked]
  change forkRow [placeRow ⟨0, 5, 4, 5⟩ (rowAt 0), placeRow ⟨91, 0, 3, 4⟩ (rowAt 91)] = data_145
  rw [row_0, row_91]
  apply row_ext <;> decide +kernel
theorem entry_good_145 : EntryGood 145 := by
  unfold EntryGood
  rw [entry_145_checked]
  decide +kernel
theorem good_145 : Good (rowAt 145) := by
  rw [row_145]
  unfold Good
  decide +kernel

def data_146 : RowData := ⟨{(-2, -1), (-1, -2), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)}, 4⟩
theorem entry_146_checked : entryAt 146 = entry_146 := by
  rw [entry_chunk_7 0 (by decide)]
  decide +kernel
theorem row_146 : rowAt 146 = data_146 := by
  rw [rowAt, dif_neg (by decide : ¬ 146 < 6), entry_146_checked]
  change forkRow [placeRow ⟨36, 6, 5, 4⟩ (rowAt 36), placeRow ⟨24, 1, 4, 5⟩ (rowAt 24)] = data_146
  rw [row_36, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_146 : EntryGood 146 := by
  unfold EntryGood
  rw [entry_146_checked]
  decide +kernel
theorem good_146 : Good (rowAt 146) := by
  rw [row_146]
  unfold Good
  decide +kernel

def data_147 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-2, 2), (-2, 3), (-1, 0)}, {(-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)}, 5⟩
theorem entry_147_checked : entryAt 147 = entry_147 := by
  rw [entry_chunk_7 1 (by decide)]
  decide +kernel
theorem row_147 : rowAt 147 = data_147 := by
  rw [rowAt, dif_neg (by decide : ¬ 147 < 6), entry_147_checked]
  change forkRow [placeRow ⟨53, 0, 1, 5⟩ (rowAt 53), placeRow ⟨44, 2, 5, 4⟩ (rowAt 44)] = data_147
  rw [row_53, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_147 : EntryGood 147 := by
  unfold EntryGood
  rw [entry_147_checked]
  decide +kernel
theorem good_147 : Good (rowAt 147) := by
  rw [row_147]
  unfold Good
  decide +kernel

def data_148 : RowData := ⟨{(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (1, -2)}, {(-1, -3), (-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)}, 6⟩
theorem entry_148_checked : entryAt 148 = entry_148 := by
  rw [entry_chunk_7 2 (by decide)]
  decide +kernel
theorem row_148 : rowAt 148 = data_148 := by
  rw [rowAt, dif_neg (by decide : ¬ 148 < 6), entry_148_checked]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (rowAt 7), placeRow ⟨46, 1, 4, 5⟩ (rowAt 46), placeRow ⟨94, 0, 5, 3⟩ (rowAt 94), placeRow ⟨97, 1, 4, 5⟩ (rowAt 97)] = data_148
  rw [row_7, row_46, row_94, row_97]
  apply row_ext <;> decide +kernel
theorem entry_good_148 : EntryGood 148 := by
  unfold EntryGood
  rw [entry_148_checked]
  decide +kernel
theorem good_148 : Good (rowAt 148) := by
  rw [row_148]
  unfold Good
  decide +kernel

def data_149 : RowData := ⟨{(-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, 1)}, {(-3, 1), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (3, 0)}, 4⟩
theorem entry_149_checked : entryAt 149 = entry_149 := by
  rw [entry_chunk_7 3 (by decide)]
  decide +kernel
theorem row_149 : rowAt 149 = data_149 := by
  rw [rowAt, dif_neg (by decide : ¬ 149 < 6), entry_149_checked]
  change forkRow [placeRow ⟨16, 1, 4, 3⟩ (rowAt 16), placeRow ⟨24, 2, 5, 4⟩ (rowAt 24)] = data_149
  rw [row_16, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_149 : EntryGood 149 := by
  unfold EntryGood
  rw [entry_149_checked]
  decide +kernel
theorem good_149 : Good (rowAt 149) := by
  rw [row_149]
  unfold Good
  decide +kernel

def data_150 : RowData := ⟨{(-5, 0), (-4, -1), (-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)}, 6⟩
theorem entry_150_checked : entryAt 150 = entry_150 := by
  rw [entry_chunk_7 4 (by decide)]
  decide +kernel
theorem row_150 : rowAt 150 = data_150 := by
  rw [rowAt, dif_neg (by decide : ¬ 150 < 6), entry_150_checked]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (rowAt 4), placeRow ⟨126, 5, 2, 5⟩ (rowAt 126)] = data_150
  rw [row_4, row_126]
  apply row_ext <;> decide +kernel
theorem entry_good_150 : EntryGood 150 := by
  unfold EntryGood
  rw [entry_150_checked]
  decide +kernel
theorem good_150 : Good (rowAt 150) := by
  rw [row_150]
  unfold Good
  decide +kernel

def data_151 : RowData := ⟨{(0, -3), (0, -2), (1, 0), (1, 1), (2, -2), (2, 0)}, {(-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (5, -1)}, 5⟩
theorem entry_151_checked : entryAt 151 = entry_151 := by
  rw [entry_chunk_7 5 (by decide)]
  decide +kernel
theorem row_151 : rowAt 151 = data_151 := by
  rw [rowAt, dif_neg (by decide : ¬ 151 < 6), entry_151_checked]
  change forkRow [placeRow ⟨2, 1, 4, 3⟩ (rowAt 2), placeRow ⟨101, 2, 6, 3⟩ (rowAt 101)] = data_151
  rw [row_2, row_101]
  apply row_ext <;> decide +kernel
theorem entry_good_151 : EntryGood 151 := by
  unfold EntryGood
  rw [entry_151_checked]
  decide +kernel
theorem good_151 : Good (rowAt 151) := by
  rw [row_151]
  unfold Good
  decide +kernel

def data_152 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (4, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 6⟩
theorem entry_152_checked : entryAt 152 = entry_152 := by
  rw [entry_chunk_7 6 (by decide)]
  decide +kernel
theorem row_152 : rowAt 152 = data_152 := by
  rw [rowAt, dif_neg (by decide : ¬ 152 < 6), entry_152_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨73, 1, 7, 4⟩ (rowAt 73)] = data_152
  rw [row_6, row_73]
  apply row_ext <;> decide +kernel
theorem entry_good_152 : EntryGood 152 := by
  unfold EntryGood
  rw [entry_152_checked]
  decide +kernel
theorem good_152 : Good (rowAt 152) := by
  rw [row_152]
  unfold Good
  decide +kernel

def data_153 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0)}, {(-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0)}, 5⟩
theorem entry_153_checked : entryAt 153 = entry_153 := by
  rw [entry_chunk_7 7 (by decide)]
  decide +kernel
theorem row_153 : rowAt 153 = data_153 := by
  rw [rowAt, dif_neg (by decide : ¬ 153 < 6), entry_153_checked]
  change forkRow [placeRow ⟨59, 4, 0, 4⟩ (rowAt 59), placeRow ⟨27, 0, 5, 4⟩ (rowAt 27)] = data_153
  rw [row_59, row_27]
  apply row_ext <;> decide +kernel
theorem entry_good_153 : EntryGood 153 := by
  unfold EntryGood
  rw [entry_153_checked]
  decide +kernel
theorem good_153 : Good (rowAt 153) := by
  rw [row_153]
  unfold Good
  decide +kernel

def data_154 : RowData := ⟨{(1, 0), (2, 0), (3, 0), (4, 0)}, {(-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (6, 0)}, 6⟩
theorem entry_154_checked : entryAt 154 = entry_154 := by
  rw [entry_chunk_7 8 (by decide)]
  decide +kernel
theorem row_154 : rowAt 154 = data_154 := by
  rw [rowAt, dif_neg (by decide : ¬ 154 < 6), entry_154_checked]
  change forkRow [placeRow ⟨7, 6, 4, 3⟩ (rowAt 7), placeRow ⟨104, 0, 7, 5⟩ (rowAt 104)] = data_154
  rw [row_7, row_104]
  apply row_ext <;> decide +kernel
theorem entry_good_154 : EntryGood 154 := by
  unfold EntryGood
  rw [entry_154_checked]
  decide +kernel
theorem good_154 : Good (rowAt 154) := by
  rw [row_154]
  unfold Good
  decide +kernel

def data_155 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)}, 5⟩
theorem entry_155_checked : entryAt 155 = entry_155 := by
  rw [entry_chunk_7 9 (by decide)]
  decide +kernel
theorem row_155 : rowAt 155 = data_155 := by
  rw [rowAt, dif_neg (by decide : ¬ 155 < 6), entry_155_checked]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (rowAt 7), placeRow ⟨55, 3, 4, 5⟩ (rowAt 55)] = data_155
  rw [row_7, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_155 : EntryGood 155 := by
  unfold EntryGood
  rw [entry_155_checked]
  decide +kernel
theorem good_155 : Good (rowAt 155) := by
  rw [row_155]
  unfold Good
  decide +kernel

def data_156 : RowData := ⟨{(-3, -1), (-3, 0), (-3, 1), (-1, -1), (-1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0)}, 6⟩
theorem entry_156_checked : entryAt 156 = entry_156 := by
  rw [entry_chunk_7 10 (by decide)]
  decide +kernel
theorem row_156 : rowAt 156 = data_156 := by
  rw [rowAt, dif_neg (by decide : ¬ 156 < 6), entry_156_checked]
  change forkRow [placeRow ⟨11, 0, 2, 4⟩ (rowAt 11), placeRow ⟨98, 2, 2, 4⟩ (rowAt 98), placeRow ⟨33, 0, 2, 3⟩ (rowAt 33)] = data_156
  rw [row_11, row_98, row_33]
  apply row_ext <;> decide +kernel
theorem entry_good_156 : EntryGood 156 := by
  unfold EntryGood
  rw [entry_156_checked]
  decide +kernel
theorem good_156 : Good (rowAt 156) := by
  rw [row_156]
  unfold Good
  decide +kernel

def data_157 : RowData := ⟨{(0, -1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1)}, {(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)}, 5⟩
theorem entry_157_checked : entryAt 157 = entry_157 := by
  rw [entry_chunk_7 11 (by decide)]
  decide +kernel
theorem row_157 : rowAt 157 = data_157 := by
  rw [rowAt, dif_neg (by decide : ¬ 157 < 6), entry_157_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨57, 1, 5, 6⟩ (rowAt 57)] = data_157
  rw [row_6, row_57]
  apply row_ext <;> decide +kernel
theorem entry_good_157 : EntryGood 157 := by
  unfold EntryGood
  rw [entry_157_checked]
  decide +kernel
theorem good_157 : Good (rowAt 157) := by
  rw [row_157]
  unfold Good
  decide +kernel

def data_158 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (3, -1)}, 5⟩
theorem entry_158_checked : entryAt 158 = entry_158 := by
  rw [entry_chunk_7 12 (by decide)]
  decide +kernel
theorem row_158 : rowAt 158 = data_158 := by
  rw [rowAt, dif_neg (by decide : ¬ 158 < 6), entry_158_checked]
  change forkRow [placeRow ⟨66, 0, 3, 4⟩ (rowAt 66), placeRow ⟨45, 1, 4, 5⟩ (rowAt 45), placeRow ⟨46, 3, 4, 5⟩ (rowAt 46)] = data_158
  rw [row_66, row_45, row_46]
  apply row_ext <;> decide +kernel
theorem entry_good_158 : EntryGood 158 := by
  unfold EntryGood
  rw [entry_158_checked]
  decide +kernel
theorem good_158 : Good (rowAt 158) := by
  rw [row_158]
  unfold Good
  decide +kernel

def data_159 : RowData := ⟨{(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3)}, 6⟩
theorem entry_159_checked : entryAt 159 = entry_159 := by
  rw [entry_chunk_7 13 (by decide)]
  decide +kernel
theorem row_159 : rowAt 159 = data_159 := by
  rw [rowAt, dif_neg (by decide : ¬ 159 < 6), entry_159_checked]
  change forkRow [placeRow ⟨45, 3, 4, 5⟩ (rowAt 45), placeRow ⟨65, 1, 4, 5⟩ (rowAt 65), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7)] = data_159
  rw [row_45, row_65, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_159 : EntryGood 159 := by
  unfold EntryGood
  rw [entry_159_checked]
  decide +kernel
theorem good_159 : Good (rowAt 159) := by
  rw [row_159]
  unfold Good
  decide +kernel

#check row_159
def data_160 : RowData := ⟨{(1, 0), (1, 1), (1, 2), (2, 0), (3, 0)}, {(-1, -1), (0, -1), (0, 0), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 6⟩
theorem entry_160_checked : entryAt 160 = entry_160 := by
  rw [entry_chunk_7 14 (by decide)]
  decide +kernel
theorem row_160 : rowAt 160 = data_160 := by
  rw [rowAt, dif_neg (by decide : ¬ 160 < 6), entry_160_checked]
  change forkRow [placeRow ⟨63, 1, 8, 3⟩ (rowAt 63), placeRow ⟨32, 3, 4, 3⟩ (rowAt 32)] = data_160
  rw [row_63, row_32]
  apply row_ext <;> decide +kernel
theorem entry_good_160 : EntryGood 160 := by
  unfold EntryGood
  rw [entry_160_checked]
  decide +kernel
theorem good_160 : Good (rowAt 160) := by
  rw [row_160]
  unfold Good
  decide +kernel

def data_161 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, 2)}, {(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)}, 6⟩
theorem entry_161_checked : entryAt 161 = entry_161 := by
  rw [entry_chunk_7 15 (by decide)]
  decide +kernel
theorem row_161 : rowAt 161 = data_161 := by
  rw [rowAt, dif_neg (by decide : ¬ 161 < 6), entry_161_checked]
  change forkRow [placeRow ⟨15, 1, 4, 5⟩ (rowAt 15), placeRow ⟨86, 0, 5, 4⟩ (rowAt 86)] = data_161
  rw [row_15, row_86]
  apply row_ext <;> decide +kernel
theorem entry_good_161 : EntryGood 161 := by
  unfold EntryGood
  rw [entry_161_checked]
  decide +kernel
theorem good_161 : Good (rowAt 161) := by
  rw [row_161]
  unfold Good
  decide +kernel

def data_162 : RowData := ⟨{(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)}, 6⟩
theorem entry_162_checked : entryAt 162 = entry_162 := by
  rw [entry_chunk_7 16 (by decide)]
  decide +kernel
theorem row_162 : rowAt 162 = data_162 := by
  rw [rowAt, dif_neg (by decide : ¬ 162 < 6), entry_162_checked]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨127, 1, 4, 5⟩ (rowAt 127), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨157, 0, 3, 3⟩ (rowAt 157)] = data_162
  rw [row_7, row_127, row_63, row_157]
  apply row_ext <;> decide +kernel
theorem entry_good_162 : EntryGood 162 := by
  unfold EntryGood
  rw [entry_162_checked]
  decide +kernel
theorem good_162 : Good (rowAt 162) := by
  rw [row_162]
  unfold Good
  decide +kernel

def data_163 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 5⟩
theorem entry_163_checked : entryAt 163 = entry_163 := by
  rw [entry_chunk_7 17 (by decide)]
  decide +kernel
theorem row_163 : rowAt 163 = data_163 := by
  rw [rowAt, dif_neg (by decide : ¬ 163 < 6), entry_163_checked]
  change forkRow [placeRow ⟨44, 2, 5, 4⟩ (rowAt 44), placeRow ⟨49, 1, 5, 4⟩ (rowAt 49), placeRow ⟨56, 4, 0, 4⟩ (rowAt 56)] = data_163
  rw [row_44, row_49, row_56]
  apply row_ext <;> decide +kernel
theorem entry_good_163 : EntryGood 163 := by
  unfold EntryGood
  rw [entry_163_checked]
  decide +kernel
theorem good_163 : Good (rowAt 163) := by
  rw [row_163]
  unfold Good
  decide +kernel

def data_164 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, 0)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 7⟩
theorem entry_164_checked : entryAt 164 = entry_164 := by
  rw [entry_chunk_7 18 (by decide)]
  decide +kernel
theorem row_164 : rowAt 164 = data_164 := by
  rw [rowAt, dif_neg (by decide : ¬ 164 < 6), entry_164_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨110, 0, 5, 4⟩ (rowAt 110)] = data_164
  rw [row_6, row_110]
  apply row_ext <;> decide +kernel
theorem entry_good_164 : EntryGood 164 := by
  unfold EntryGood
  rw [entry_164_checked]
  decide +kernel
theorem good_164 : Good (rowAt 164) := by
  rw [row_164]
  unfold Good
  decide +kernel

def data_165 : RowData := ⟨{(0, 1), (1, 1), (1, 2), (1, 3), (2, 1)}, {(-1, 0), (0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)}, 7⟩
theorem entry_165_checked : entryAt 165 = entry_165 := by
  rw [entry_chunk_7 19 (by decide)]
  decide +kernel
theorem row_165 : rowAt 165 = data_165 := by
  rw [rowAt, dif_neg (by decide : ¬ 165 < 6), entry_165_checked]
  change forkRow [placeRow ⟨0, 7, 5, 8⟩ (rowAt 0), placeRow ⟨107, 0, 7, 5⟩ (rowAt 107)] = data_165
  rw [row_0, row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_165 : EntryGood 165 := by
  unfold EntryGood
  rw [entry_165_checked]
  decide +kernel
theorem good_165 : Good (rowAt 165) := by
  rw [row_165]
  unfold Good
  decide +kernel

def data_166 : RowData := ⟨{(-1, -1), (-1, 0), (0, 2), (0, 3), (1, 0)}, {(-2, -1), (-1, -1), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 7⟩
theorem entry_166_checked : entryAt 166 = entry_166 := by
  rw [entry_chunk_8 0 (by decide)]
  decide +kernel
theorem row_166 : rowAt 166 = data_166 := by
  rw [rowAt, dif_neg (by decide : ¬ 166 < 6), entry_166_checked]
  change forkRow [placeRow ⟨2, 7, 4, 5⟩ (rowAt 2), placeRow ⟨107, 0, 6, 4⟩ (rowAt 107)] = data_166
  rw [row_2, row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_166 : EntryGood 166 := by
  unfold EntryGood
  rw [entry_166_checked]
  decide +kernel
theorem good_166 : Good (rowAt 166) := by
  rw [row_166]
  unfold Good
  decide +kernel

def data_167 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0)}, {(-5, 0), (-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)}, 5⟩
theorem entry_167_checked : entryAt 167 = entry_167 := by
  rw [entry_chunk_8 1 (by decide)]
  decide +kernel
theorem row_167 : rowAt 167 = data_167 := by
  rw [rowAt, dif_neg (by decide : ¬ 167 < 6), entry_167_checked]
  change forkRow [placeRow ⟨57, 0, 5, 4⟩ (rowAt 57), placeRow ⟨57, 4, 0, 4⟩ (rowAt 57)] = data_167
  rw [row_57]
  apply row_ext <;> decide +kernel
theorem entry_good_167 : EntryGood 167 := by
  unfold EntryGood
  rw [entry_167_checked]
  decide +kernel
theorem good_167 : Good (rowAt 167) := by
  rw [row_167]
  unfold Good
  decide +kernel

def data_168 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, 0), (3, -1)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 7⟩
theorem entry_168_checked : entryAt 168 = entry_168 := by
  rw [entry_chunk_8 2 (by decide)]
  decide +kernel
theorem row_168 : rowAt 168 = data_168 := by
  rw [rowAt, dif_neg (by decide : ¬ 168 < 6), entry_168_checked]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (rowAt 6), placeRow ⟨152, 0, 3, 4⟩ (rowAt 152)] = data_168
  rw [row_6, row_152]
  apply row_ext <;> decide +kernel
theorem entry_good_168 : EntryGood 168 := by
  unfold EntryGood
  rw [entry_168_checked]
  decide +kernel
theorem good_168 : Good (rowAt 168) := by
  rw [row_168]
  unfold Good
  decide +kernel

def data_169 : RowData := ⟨{(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)}, {(-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 6⟩
theorem entry_169_checked : entryAt 169 = entry_169 := by
  rw [entry_chunk_8 3 (by decide)]
  decide +kernel
theorem row_169 : rowAt 169 = data_169 := by
  rw [rowAt, dif_neg (by decide : ¬ 169 < 6), entry_169_checked]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (rowAt 28), placeRow ⟨63, 1, 8, 3⟩ (rowAt 63)] = data_169
  rw [row_28, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_169 : EntryGood 169 := by
  unfold EntryGood
  rw [entry_169_checked]
  decide +kernel
theorem good_169 : Good (rowAt 169) := by
  rw [row_169]
  unfold Good
  decide +kernel

def data_170 : RowData := ⟨{(-4, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, 1)}, 6⟩
theorem entry_170_checked : entryAt 170 = entry_170 := by
  rw [entry_chunk_8 4 (by decide)]
  decide +kernel
theorem row_170 : rowAt 170 = data_170 := by
  rw [rowAt, dif_neg (by decide : ¬ 170 < 6), entry_170_checked]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (rowAt 4), placeRow ⟨127, 2, 5, 4⟩ (rowAt 127)] = data_170
  rw [row_4, row_127]
  apply row_ext <;> decide +kernel
theorem entry_good_170 : EntryGood 170 := by
  unfold EntryGood
  rw [entry_170_checked]
  decide +kernel
theorem good_170 : Good (rowAt 170) := by
  rw [row_170]
  unfold Good
  decide +kernel

def data_171 : RowData := ⟨{(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)}, {(-4, 1), (-4, 2), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, 0)}, 6⟩
theorem entry_171_checked : entryAt 171 = entry_171 := by
  rw [entry_chunk_8 5 (by decide)]
  decide +kernel
theorem row_171 : rowAt 171 = data_171 := by
  rw [rowAt, dif_neg (by decide : ¬ 171 < 6), entry_171_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨91, 0, 0, 5⟩ (rowAt 91)] = data_171
  rw [row_6, row_91]
  apply row_ext <;> decide +kernel
theorem entry_good_171 : EntryGood 171 := by
  unfold EntryGood
  rw [entry_171_checked]
  decide +kernel
theorem good_171 : Good (rowAt 171) := by
  rw [row_171]
  unfold Good
  decide +kernel

def data_172 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 6⟩
theorem entry_172_checked : entryAt 172 = entry_172 := by
  rw [entry_chunk_8 6 (by decide)]
  decide +kernel
theorem row_172 : rowAt 172 = data_172 := by
  rw [rowAt, dif_neg (by decide : ¬ 172 < 6), entry_172_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨55, 6, 0, 4⟩ (rowAt 55), placeRow ⟨64, 0, 1, 3⟩ (rowAt 64)] = data_172
  rw [row_63, row_55, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_172 : EntryGood 172 := by
  unfold EntryGood
  rw [entry_172_checked]
  decide +kernel
theorem good_172 : Good (rowAt 172) := by
  rw [row_172]
  unfold Good
  decide +kernel

def data_173 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 6⟩
theorem entry_173_checked : entryAt 173 = entry_173 := by
  rw [entry_chunk_8 7 (by decide)]
  decide +kernel
theorem row_173 : rowAt 173 = data_173 := by
  rw [rowAt, dif_neg (by decide : ¬ 173 < 6), entry_173_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨64, 6, 4, 5⟩ (rowAt 64), placeRow ⟨55, 6, 0, 4⟩ (rowAt 55)] = data_173
  rw [row_63, row_64, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_173 : EntryGood 173 := by
  unfold EntryGood
  rw [entry_173_checked]
  decide +kernel
theorem good_173 : Good (rowAt 173) := by
  rw [row_173]
  unfold Good
  decide +kernel

def data_174 : RowData := ⟨{(-1, -2), (-1, -1), (0, -3), (0, -2), (0, -1)}, {(-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (3, 0)}, 6⟩
theorem entry_174_checked : entryAt 174 = entry_174 := by
  rw [entry_chunk_8 8 (by decide)]
  decide +kernel
theorem row_174 : rowAt 174 = data_174 := by
  rw [rowAt, dif_neg (by decide : ¬ 174 < 6), entry_174_checked]
  change forkRow [placeRow ⟨58, 3, 4, 5⟩ (rowAt 58), placeRow ⟨57, 1, 4, 5⟩ (rowAt 57), placeRow ⟨84, 0, 3, 4⟩ (rowAt 84)] = data_174
  rw [row_58, row_57, row_84]
  apply row_ext <;> decide +kernel
theorem entry_good_174 : EntryGood 174 := by
  unfold EntryGood
  rw [entry_174_checked]
  decide +kernel
theorem good_174 : Good (rowAt 174) := by
  rw [row_174]
  unfold Good
  decide +kernel

def data_175 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-5, 0), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)}, 6⟩
theorem entry_175_checked : entryAt 175 = entry_175 := by
  rw [entry_chunk_8 9 (by decide)]
  decide +kernel
theorem row_175 : rowAt 175 = data_175 := by
  rw [rowAt, dif_neg (by decide : ¬ 175 < 6), entry_175_checked]
  change forkRow [placeRow ⟨141, 0, 5, 4⟩ (rowAt 141), placeRow ⟨7, 2, 4, 3⟩ (rowAt 7), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63)] = data_175
  rw [row_141, row_7, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_175 : EntryGood 175 := by
  unfold EntryGood
  rw [entry_175_checked]
  decide +kernel
theorem good_175 : Good (rowAt 175) := by
  rw [row_175]
  unfold Good
  decide +kernel

def data_176 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 6⟩
theorem entry_176_checked : entryAt 176 = entry_176 := by
  rw [entry_chunk_8 10 (by decide)]
  decide +kernel
theorem row_176 : rowAt 176 = data_176 := by
  rw [rowAt, dif_neg (by decide : ¬ 176 < 6), entry_176_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨64, 6, 4, 5⟩ (rowAt 64), placeRow ⟨55, 2, 5, 4⟩ (rowAt 55)] = data_176
  rw [row_63, row_64, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_176 : EntryGood 176 := by
  unfold EntryGood
  rw [entry_176_checked]
  decide +kernel
theorem good_176 : Good (rowAt 176) := by
  rw [row_176]
  unfold Good
  decide +kernel

def data_177 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, -2), (2, 0)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (3, -1)}, 6⟩
theorem entry_177_checked : entryAt 177 = entry_177 := by
  rw [entry_chunk_8 11 (by decide)]
  decide +kernel
theorem row_177 : rowAt 177 = data_177 := by
  rw [rowAt, dif_neg (by decide : ¬ 177 < 6), entry_177_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨136, 3, 5, 4⟩ (rowAt 136)] = data_177
  rw [row_6, row_136]
  apply row_ext <;> decide +kernel
theorem entry_good_177 : EntryGood 177 := by
  unfold EntryGood
  rw [entry_177_checked]
  decide +kernel
theorem good_177 : Good (rowAt 177) := by
  rw [row_177]
  unfold Good
  decide +kernel

def data_178 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -1), (3, -1)}, 6⟩
theorem entry_178_checked : entryAt 178 = entry_178 := by
  rw [entry_chunk_8 12 (by decide)]
  decide +kernel
theorem row_178 : rowAt 178 = data_178 := by
  rw [rowAt, dif_neg (by decide : ¬ 178 < 6), entry_178_checked]
  change forkRow [placeRow ⟨37, 0, 3, 4⟩ (rowAt 37), placeRow ⟨68, 1, 4, 5⟩ (rowAt 68), placeRow ⟨46, 3, 4, 5⟩ (rowAt 46)] = data_178
  rw [row_37, row_68, row_46]
  apply row_ext <;> decide +kernel
theorem entry_good_178 : EntryGood 178 := by
  unfold EntryGood
  rw [entry_178_checked]
  decide +kernel
theorem good_178 : Good (rowAt 178) := by
  rw [row_178]
  unfold Good
  decide +kernel

def data_179 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 1)}, {(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1)}, 7⟩
theorem entry_179_checked : entryAt 179 = entry_179 := by
  rw [entry_chunk_8 13 (by decide)]
  decide +kernel
theorem row_179 : rowAt 179 = data_179 := by
  rw [rowAt, dif_neg (by decide : ¬ 179 < 6), entry_179_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨148, 5, 5, 4⟩ (rowAt 148)] = data_179
  rw [row_6, row_148]
  apply row_ext <;> decide +kernel
theorem entry_good_179 : EntryGood 179 := by
  unfold EntryGood
  rw [entry_179_checked]
  decide +kernel
theorem good_179 : Good (rowAt 179) := by
  rw [row_179]
  unfold Good
  decide +kernel

def data_180 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)}, 6⟩
theorem entry_180_checked : entryAt 180 = entry_180 := by
  rw [entry_chunk_8 14 (by decide)]
  decide +kernel
theorem row_180 : rowAt 180 = data_180 := by
  rw [rowAt, dif_neg (by decide : ¬ 180 < 6), entry_180_checked]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨155, 0, 4, 5⟩ (rowAt 155), placeRow ⟨132, 0, 3, 3⟩ (rowAt 132)] = data_180
  rw [row_7, row_63, row_155, row_132]
  apply row_ext <;> decide +kernel
theorem entry_good_180 : EntryGood 180 := by
  unfold EntryGood
  rw [entry_180_checked]
  decide +kernel
theorem good_180 : Good (rowAt 180) := by
  rw [row_180]
  unfold Good
  decide +kernel

def data_181 : RowData := ⟨{(1, -2), (1, -1), (1, 0), (2, 1)}, {(-2, 0), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1), (5, 1)}, 5⟩
theorem entry_181_checked : entryAt 181 = entry_181 := by
  rw [entry_chunk_8 15 (by decide)]
  decide +kernel
theorem row_181 : rowAt 181 = data_181 := by
  rw [rowAt, dif_neg (by decide : ¬ 181 < 6), entry_181_checked]
  change forkRow [placeRow ⟨24, 3, 4, 5⟩ (rowAt 24), placeRow ⟨87, 2, 6, 4⟩ (rowAt 87), placeRow ⟨90, 0, 7, 5⟩ (rowAt 90)] = data_181
  rw [row_24, row_87, row_90]
  apply row_ext <;> decide +kernel
theorem entry_good_181 : EntryGood 181 := by
  unfold EntryGood
  rw [entry_181_checked]
  decide +kernel
theorem good_181 : Good (rowAt 181) := by
  rw [row_181]
  unfold Good
  decide +kernel

def data_182 : RowData := ⟨{(1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, 2)}, {(-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, 0)}, 5⟩
theorem entry_182_checked : entryAt 182 = entry_182 := by
  rw [entry_chunk_8 16 (by decide)]
  decide +kernel
theorem row_182 : rowAt 182 = data_182 := by
  rw [rowAt, dif_neg (by decide : ¬ 182 < 6), entry_182_checked]
  change forkRow [placeRow ⟨12, 2, 7, 3⟩ (rowAt 12), placeRow ⟨139, 0, 7, 4⟩ (rowAt 139)] = data_182
  rw [row_12, row_139]
  apply row_ext <;> decide +kernel
theorem entry_good_182 : EntryGood 182 := by
  unfold EntryGood
  rw [entry_182_checked]
  decide +kernel
theorem good_182 : Good (rowAt 182) := by
  rw [row_182]
  unfold Good
  decide +kernel

def data_183 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)}, 6⟩
theorem entry_183_checked : entryAt 183 = entry_183 := by
  rw [entry_chunk_8 17 (by decide)]
  decide +kernel
theorem row_183 : rowAt 183 = data_183 := by
  rw [rowAt, dif_neg (by decide : ¬ 183 < 6), entry_183_checked]
  change forkRow [placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨63, 3, 0, 3⟩ (rowAt 63), placeRow ⟨55, 2, 5, 4⟩ (rowAt 55)] = data_183
  rw [row_64, row_63, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_183 : EntryGood 183 := by
  unfold EntryGood
  rw [entry_183_checked]
  decide +kernel
theorem good_183 : Good (rowAt 183) := by
  rw [row_183]
  unfold Good
  decide +kernel

def data_184 : RowData := ⟨{(0, -3), (1, -4), (1, -3), (2, -3), (2, -1), (2, 0), (3, -3), (3, -1)}, {(-1, -2), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -1), (1, 0), (2, -3), (2, -1), (2, 0), (3, -3), (3, -1), (4, -1), (5, -1)}, 4⟩
theorem entry_184_checked : entryAt 184 = entry_184 := by
  rw [entry_chunk_8 18 (by decide)]
  decide +kernel
theorem row_184 : rowAt 184 = data_184 := by
  rw [rowAt, dif_neg (by decide : ¬ 184 < 6), entry_184_checked]
  change forkRow [placeRow ⟨34, 3, 4, 2⟩ (rowAt 34), placeRow ⟨35, 2, 5, 4⟩ (rowAt 35)] = data_184
  rw [row_34, row_35]
  apply row_ext <;> decide +kernel
theorem entry_good_184 : EntryGood 184 := by
  unfold EntryGood
  rw [entry_184_checked]
  decide +kernel
theorem good_184 : Good (rowAt 184) := by
  rw [row_184]
  unfold Good
  decide +kernel

def data_185 : RowData := ⟨{(-1, -3), (-1, -1), (0, -3), (0, -2), (0, -1)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (3, 0)}, 6⟩
theorem entry_185_checked : entryAt 185 = entry_185 := by
  rw [entry_chunk_8 19 (by decide)]
  decide +kernel
theorem row_185 : rowAt 185 = data_185 := by
  rw [rowAt, dif_neg (by decide : ¬ 185 < 6), entry_185_checked]
  change forkRow [placeRow ⟨44, 3, 4, 5⟩ (rowAt 44), placeRow ⟨49, 0, 4, 5⟩ (rowAt 49), placeRow ⟨84, 0, 3, 4⟩ (rowAt 84)] = data_185
  rw [row_44, row_49, row_84]
  apply row_ext <;> decide +kernel
theorem entry_good_185 : EntryGood 185 := by
  unfold EntryGood
  rw [entry_185_checked]
  decide +kernel
theorem good_185 : Good (rowAt 185) := by
  rw [row_185]
  unfold Good
  decide +kernel

def data_186 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0)}, 5⟩
theorem entry_186_checked : entryAt 186 = entry_186 := by
  rw [entry_chunk_9 0 (by decide)]
  decide +kernel
theorem row_186 : rowAt 186 = data_186 := by
  rw [rowAt, dif_neg (by decide : ¬ 186 < 6), entry_186_checked]
  change forkRow [placeRow ⟨7, 6, 0, 3⟩ (rowAt 7), placeRow ⟨141, 2, 5, 4⟩ (rowAt 141)] = data_186
  rw [row_7, row_141]
  apply row_ext <;> decide +kernel
theorem entry_good_186 : EntryGood 186 := by
  unfold EntryGood
  rw [entry_186_checked]
  decide +kernel
theorem good_186 : Good (rowAt 186) := by
  rw [row_186]
  unfold Good
  decide +kernel

def data_187 : RowData := ⟨{(0, -2), (0, -1), (1, -3), (1, -1), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -1), (3, -1)}, 7⟩
theorem entry_187_checked : entryAt 187 = entry_187 := by
  rw [entry_chunk_9 1 (by decide)]
  decide +kernel
theorem row_187 : rowAt 187 = data_187 := by
  rw [rowAt, dif_neg (by decide : ¬ 187 < 6), entry_187_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨108, 3, 4, 5⟩ (rowAt 108)] = data_187
  rw [row_6, row_108]
  apply row_ext <;> decide +kernel
theorem entry_good_187 : EntryGood 187 := by
  unfold EntryGood
  rw [entry_187_checked]
  decide +kernel
theorem good_187 : Good (rowAt 187) := by
  rw [row_187]
  unfold Good
  decide +kernel

def data_188 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -2), (4, -2), (4, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (4, 1), (5, 1)}, 6⟩
theorem entry_188_checked : entryAt 188 = entry_188 := by
  rw [entry_chunk_9 2 (by decide)]
  decide +kernel
theorem row_188 : rowAt 188 = data_188 := by
  rw [rowAt, dif_neg (by decide : ¬ 188 < 6), entry_188_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨112, 5, 7, 4⟩ (rowAt 112)] = data_188
  rw [row_6, row_112]
  apply row_ext <;> decide +kernel
theorem entry_good_188 : EntryGood 188 := by
  unfold EntryGood
  rw [entry_188_checked]
  decide +kernel
theorem good_188 : Good (rowAt 188) := by
  rw [row_188]
  unfold Good
  decide +kernel

def data_189 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0)}, 6⟩
theorem entry_189_checked : entryAt 189 = entry_189 := by
  rw [entry_chunk_9 3 (by decide)]
  decide +kernel
theorem row_189 : rowAt 189 = data_189 := by
  rw [rowAt, dif_neg (by decide : ¬ 189 < 6), entry_189_checked]
  change forkRow [placeRow ⟨12, 0, 5, 4⟩ (rowAt 12), placeRow ⟨86, 4, 1, 4⟩ (rowAt 86)] = data_189
  rw [row_12, row_86]
  apply row_ext <;> decide +kernel
theorem entry_good_189 : EntryGood 189 := by
  unfold EntryGood
  rw [entry_189_checked]
  decide +kernel
theorem good_189 : Good (rowAt 189) := by
  rw [row_189]
  unfold Good
  decide +kernel

def data_190 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, 0)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1)}, 7⟩
theorem entry_190_checked : entryAt 190 = entry_190 := by
  rw [entry_chunk_9 4 (by decide)]
  decide +kernel
theorem row_190 : rowAt 190 = data_190 := by
  rw [rowAt, dif_neg (by decide : ¬ 190 < 6), entry_190_checked]
  change forkRow [placeRow ⟨46, 0, 5, 4⟩ (rowAt 46), placeRow ⟨85, 2, 3, 3⟩ (rowAt 85), placeRow ⟨111, 3, 4, 3⟩ (rowAt 111)] = data_190
  rw [row_46, row_85, row_111]
  apply row_ext <;> decide +kernel
theorem entry_good_190 : EntryGood 190 := by
  unfold EntryGood
  rw [entry_190_checked]
  decide +kernel
theorem good_190 : Good (rowAt 190) := by
  rw [row_190]
  unfold Good
  decide +kernel

def data_191 : RowData := ⟨{(0, -2), (0, -1), (1, -2), (1, -1), (2, -1), (3, -1), (3, 0)}, {(-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0)}, 7⟩
theorem entry_191_checked : entryAt 191 = entry_191 := by
  rw [entry_chunk_9 5 (by decide)]
  decide +kernel
theorem row_191 : rowAt 191 = data_191 := by
  rw [rowAt, dif_neg (by decide : ¬ 191 < 6), entry_191_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨145, 0, 4, 5⟩ (rowAt 145)] = data_191
  rw [row_6, row_145]
  apply row_ext <;> decide +kernel
theorem entry_good_191 : EntryGood 191 := by
  unfold EntryGood
  rw [entry_191_checked]
  decide +kernel
theorem good_191 : Good (rowAt 191) := by
  rw [row_191]
  unfold Good
  decide +kernel

#check row_191
def data_192 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (2, -1)}, {(-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (3, -1)}, 6⟩
theorem entry_192_checked : entryAt 192 = entry_192 := by
  rw [entry_chunk_9 6 (by decide)]
  decide +kernel
theorem row_192 : rowAt 192 = data_192 := by
  rw [rowAt, dif_neg (by decide : ¬ 192 < 6), entry_192_checked]
  change forkRow [placeRow ⟨64, 1, 3, 1⟩ (rowAt 64), placeRow ⟨103, 0, 3, 4⟩ (rowAt 103), placeRow ⟨55, 3, 4, 5⟩ (rowAt 55)] = data_192
  rw [row_64, row_103, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_192 : EntryGood 192 := by
  unfold EntryGood
  rw [entry_192_checked]
  decide +kernel
theorem good_192 : Good (rowAt 192) := by
  rw [row_192]
  unfold Good
  decide +kernel

def data_193 : RowData := ⟨{(-1, -1), (-1, 0), (1, -1), (1, 0), (2, 0)}, {(-2, -1), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 7⟩
theorem entry_193_checked : entryAt 193 = entry_193 := by
  rw [entry_chunk_9 7 (by decide)]
  decide +kernel
theorem row_193 : rowAt 193 = data_193 := by
  rw [rowAt, dif_neg (by decide : ¬ 193 < 6), entry_193_checked]
  change forkRow [placeRow ⟨6, 6, 2, 3⟩ (rowAt 6), placeRow ⟨162, 1, 7, 4⟩ (rowAt 162)] = data_193
  rw [row_6, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_193 : EntryGood 193 := by
  unfold EntryGood
  rw [entry_193_checked]
  decide +kernel
theorem good_193 : Good (rowAt 193) := by
  rw [row_193]
  unfold Good
  decide +kernel

def data_194 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0), (-1, 1)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 1), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, 0), (2, 0)}, 5⟩
theorem entry_194_checked : entryAt 194 = entry_194 := by
  rw [entry_chunk_9 8 (by decide)]
  decide +kernel
theorem row_194 : rowAt 194 = data_194 := by
  rw [rowAt, dif_neg (by decide : ¬ 194 < 6), entry_194_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨146, 4, 2, 5⟩ (rowAt 146)] = data_194
  rw [row_0, row_146]
  apply row_ext <;> decide +kernel
theorem entry_good_194 : EntryGood 194 := by
  unfold EntryGood
  rw [entry_194_checked]
  decide +kernel
theorem good_194 : Good (rowAt 194) := by
  rw [row_194]
  unfold Good
  decide +kernel

def data_195 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 7⟩
theorem entry_195_checked : entryAt 195 = entry_195 := by
  rw [entry_chunk_9 9 (by decide)]
  decide +kernel
theorem row_195 : rowAt 195 = data_195 := by
  rw [rowAt, dif_neg (by decide : ¬ 195 < 6), entry_195_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨162, 1, 5, 4⟩ (rowAt 162)] = data_195
  rw [row_6, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_195 : EntryGood 195 := by
  unfold EntryGood
  rw [entry_195_checked]
  decide +kernel
theorem good_195 : Good (rowAt 195) := by
  rw [row_195]
  unfold Good
  decide +kernel

def data_196 : RowData := ⟨{(-1, -1), (1, -3), (1, -2), (1, -1), (1, 0)}, {(-1, -1), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 8⟩
theorem entry_196_checked : entryAt 196 = entry_196 := by
  rw [entry_chunk_9 10 (by decide)]
  decide +kernel
theorem row_196 : rowAt 196 = data_196 := by
  rw [rowAt, dif_neg (by decide : ¬ 196 < 6), entry_196_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨187, 5, 6, 4⟩ (rowAt 187)] = data_196
  rw [row_6, row_187]
  apply row_ext <;> decide +kernel
theorem entry_good_196 : EntryGood 196 := by
  unfold EntryGood
  rw [entry_196_checked]
  decide +kernel
theorem good_196 : Good (rowAt 196) := by
  rw [row_196]
  unfold Good
  decide +kernel

def data_197 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 6⟩
theorem entry_197_checked : entryAt 197 = entry_197 := by
  rw [entry_chunk_9 11 (by decide)]
  decide +kernel
theorem row_197 : rowAt 197 = data_197 := by
  rw [rowAt, dif_neg (by decide : ¬ 197 < 6), entry_197_checked]
  change forkRow [placeRow ⟨63, 3, 0, 3⟩ (rowAt 63), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63)] = data_197
  rw [row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_197 : EntryGood 197 := by
  unfold EntryGood
  rw [entry_197_checked]
  decide +kernel
theorem good_197 : Good (rowAt 197) := by
  rw [row_197]
  unfold Good
  decide +kernel

def data_198 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, -1), (-1, 0)}, {(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)}, 6⟩
theorem entry_198_checked : entryAt 198 = entry_198 := by
  rw [entry_chunk_9 12 (by decide)]
  decide +kernel
theorem row_198 : rowAt 198 = data_198 := by
  rw [rowAt, dif_neg (by decide : ¬ 198 < 6), entry_198_checked]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (rowAt 7), placeRow ⟨131, 1, 5, 4⟩ (rowAt 131)] = data_198
  rw [row_7, row_131]
  apply row_ext <;> decide +kernel
theorem entry_good_198 : EntryGood 198 := by
  unfold EntryGood
  rw [entry_198_checked]
  decide +kernel
theorem good_198 : Good (rowAt 198) := by
  rw [row_198]
  unfold Good
  decide +kernel

def data_199 : RowData := ⟨{(-1, -1), (0, -3), (0, -2), (0, -1)}, {(-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, 0), (3, 0)}, 6⟩
theorem entry_199_checked : entryAt 199 = entry_199 := by
  rw [entry_chunk_9 13 (by decide)]
  decide +kernel
theorem row_199 : rowAt 199 = data_199 := by
  rw [rowAt, dif_neg (by decide : ¬ 199 < 6), entry_199_checked]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (rowAt 55), placeRow ⟨64, 3, 5, 1⟩ (rowAt 64), placeRow ⟨84, 0, 3, 4⟩ (rowAt 84)] = data_199
  rw [row_55, row_64, row_84]
  apply row_ext <;> decide +kernel
theorem entry_good_199 : EntryGood 199 := by
  unfold EntryGood
  rw [entry_199_checked]
  decide +kernel
theorem good_199 : Good (rowAt 199) := by
  rw [row_199]
  unfold Good
  decide +kernel

def data_200 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (2, -1)}, {(-2, 0), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (3, -1)}, 6⟩
theorem entry_200_checked : entryAt 200 = entry_200 := by
  rw [entry_chunk_9 14 (by decide)]
  decide +kernel
theorem row_200 : rowAt 200 = data_200 := by
  rw [rowAt, dif_neg (by decide : ¬ 200 < 6), entry_200_checked]
  change forkRow [placeRow ⟨103, 0, 3, 4⟩ (rowAt 103), placeRow ⟨64, 3, 5, 1⟩ (rowAt 64), placeRow ⟨55, 1, 4, 5⟩ (rowAt 55)] = data_200
  rw [row_103, row_64, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_200 : EntryGood 200 := by
  unfold EntryGood
  rw [entry_200_checked]
  decide +kernel
theorem good_200 : Good (rowAt 200) := by
  rw [row_200]
  unfold Good
  decide +kernel

def data_201 : RowData := ⟨{(1, -2), (1, -1), (1, 0), (1, 1), (1, 2)}, {(-2, 0), (-1, 0), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (3, 1), (4, 1)}, 5⟩
theorem entry_201_checked : entryAt 201 = entry_201 := by
  rw [entry_chunk_9 15 (by decide)]
  decide +kernel
theorem row_201 : rowAt 201 = data_201 := by
  rw [rowAt, dif_neg (by decide : ¬ 201 < 6), entry_201_checked]
  change forkRow [placeRow ⟨45, 3, 5, 7⟩ (rowAt 45), placeRow ⟨82, 0, 6, 5⟩ (rowAt 82)] = data_201
  rw [row_45, row_82]
  apply row_ext <;> decide +kernel
theorem entry_good_201 : EntryGood 201 := by
  unfold EntryGood
  rw [entry_201_checked]
  decide +kernel
theorem good_201 : Good (rowAt 201) := by
  rw [row_201]
  unfold Good
  decide +kernel

def data_202 : RowData := ⟨{(-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 7⟩
theorem entry_202_checked : entryAt 202 = entry_202 := by
  rw [entry_chunk_9 16 (by decide)]
  decide +kernel
theorem row_202 : rowAt 202 = data_202 := by
  rw [rowAt, dif_neg (by decide : ¬ 202 < 6), entry_202_checked]
  change forkRow [placeRow ⟨150, 0, 5, 4⟩ (rowAt 150), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7), placeRow ⟨108, 0, 5, 4⟩ (rowAt 108)] = data_202
  rw [row_150, row_7, row_108]
  apply row_ext <;> decide +kernel
theorem entry_good_202 : EntryGood 202 := by
  unfold EntryGood
  rw [entry_202_checked]
  decide +kernel
theorem good_202 : Good (rowAt 202) := by
  rw [row_202]
  unfold Good
  decide +kernel

def data_203 : RowData := ⟨{(-4, -1), (-2, -1), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 7⟩
theorem entry_203_checked : entryAt 203 = entry_203 := by
  rw [entry_chunk_9 17 (by decide)]
  decide +kernel
theorem row_203 : rowAt 203 = data_203 := by
  rw [rowAt, dif_neg (by decide : ¬ 203 < 6), entry_203_checked]
  change forkRow [placeRow ⟨18, 6, 1, 3⟩ (rowAt 18), placeRow ⟨107, 0, 5, 4⟩ (rowAt 107), placeRow ⟨163, 0, 5, 4⟩ (rowAt 163)] = data_203
  rw [row_18, row_107, row_163]
  apply row_ext <;> decide +kernel
theorem entry_good_203 : EntryGood 203 := by
  unfold EntryGood
  rw [entry_203_checked]
  decide +kernel
theorem good_203 : Good (rowAt 203) := by
  rw [row_203]
  unfold Good
  decide +kernel

def data_204 : RowData := ⟨{(0, -3), (0, -1), (1, -4), (1, -3), (2, -1)}, {(-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (2, -1), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, -2), (5, 0)}, 8⟩
theorem entry_204_checked : entryAt 204 = entry_204 := by
  rw [entry_chunk_9 18 (by decide)]
  decide +kernel
theorem row_204 : rowAt 204 = data_204 := by
  rw [rowAt, dif_neg (by decide : ¬ 204 < 6), entry_204_checked]
  change forkRow [placeRow ⟨2, 5, 4, 2⟩ (rowAt 2), placeRow ⟨166, 2, 5, 3⟩ (rowAt 166)] = data_204
  rw [row_2, row_166]
  apply row_ext <;> decide +kernel
theorem entry_good_204 : EntryGood 204 := by
  unfold EntryGood
  rw [entry_204_checked]
  decide +kernel
theorem good_204 : Good (rowAt 204) := by
  rw [row_204]
  unfold Good
  decide +kernel

def data_205 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (-1, -1), (2, -1)}, {(-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 8⟩
theorem entry_205_checked : entryAt 205 = entry_205 := by
  rw [entry_chunk_9 19 (by decide)]
  decide +kernel
theorem row_205 : rowAt 205 = data_205 := by
  rw [rowAt, dif_neg (by decide : ¬ 205 < 6), entry_205_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨168, 0, 3, 4⟩ (rowAt 168)] = data_205
  rw [row_4, row_168]
  apply row_ext <;> decide +kernel
theorem entry_good_205 : EntryGood 205 := by
  unfold EntryGood
  rw [entry_205_checked]
  decide +kernel
theorem good_205 : Good (rowAt 205) := by
  rw [row_205]
  unfold Good
  decide +kernel

def data_206 : RowData := ⟨{(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)}, {(-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (5, -1), (5, 0), (6, -1)}, 6⟩
theorem entry_206_checked : entryAt 206 = entry_206 := by
  rw [entry_chunk_10 0 (by decide)]
  decide +kernel
theorem row_206 : rowAt 206 = data_206 := by
  rw [rowAt, dif_neg (by decide : ¬ 206 < 6), entry_206_checked]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (rowAt 28), placeRow ⟨135, 2, 8, 4⟩ (rowAt 135)] = data_206
  rw [row_28, row_135]
  apply row_ext <;> decide +kernel
theorem entry_good_206 : EntryGood 206 := by
  unfold EntryGood
  rw [entry_206_checked]
  decide +kernel
theorem good_206 : Good (rowAt 206) := by
  rw [row_206]
  unfold Good
  decide +kernel

def data_207 : RowData := ⟨{(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)}, {(-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (2, 0), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 6⟩
theorem entry_207_checked : entryAt 207 = entry_207 := by
  rw [entry_chunk_10 1 (by decide)]
  decide +kernel
theorem row_207 : rowAt 207 = data_207 := by
  rw [rowAt, dif_neg (by decide : ¬ 207 < 6), entry_207_checked]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (rowAt 28), placeRow ⟨127, 0, 8, 4⟩ (rowAt 127)] = data_207
  rw [row_28, row_127]
  apply row_ext <;> decide +kernel
theorem entry_good_207 : EntryGood 207 := by
  unfold EntryGood
  rw [entry_207_checked]
  decide +kernel
theorem good_207 : Good (rowAt 207) := by
  rw [row_207]
  unfold Good
  decide +kernel

def data_208 : RowData := ⟨{(-4, 0), (-3, 0), (-2, -1), (-2, 0), (-1, 0)}, {(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)}, 6⟩
theorem entry_208_checked : entryAt 208 = entry_208 := by
  rw [entry_chunk_10 2 (by decide)]
  decide +kernel
theorem row_208 : rowAt 208 = data_208 := by
  rw [rowAt, dif_neg (by decide : ¬ 208 < 6), entry_208_checked]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (rowAt 7), placeRow ⟨127, 0, 5, 4⟩ (rowAt 127)] = data_208
  rw [row_7, row_127]
  apply row_ext <;> decide +kernel
theorem entry_good_208 : EntryGood 208 := by
  unfold EntryGood
  rw [entry_208_checked]
  decide +kernel
theorem good_208 : Good (rowAt 208) := by
  rw [row_208]
  unfold Good
  decide +kernel

def data_209 : RowData := ⟨{(-3, 2), (-2, -1), (-2, 2), (-1, -1), (-1, 2), (0, -1), (0, 2)}, {(-3, -1), (-3, 2), (-2, -1), (-2, 2), (-1, -1), (-1, 0), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (2, 0), (2, 3), (3, 0)}, 5⟩
theorem entry_209_checked : entryAt 209 = entry_209 := by
  rw [entry_chunk_10 3 (by decide)]
  decide +kernel
theorem row_209 : rowAt 209 = data_209 := by
  rw [rowAt, dif_neg (by decide : ¬ 209 < 6), entry_209_checked]
  change forkRow [placeRow ⟨25, 0, 5, 4⟩ (rowAt 25), placeRow ⟨81, 5, 5, 7⟩ (rowAt 81)] = data_209
  rw [row_25, row_81]
  apply row_ext <;> decide +kernel
theorem entry_good_209 : EntryGood 209 := by
  unfold EntryGood
  rw [entry_209_checked]
  decide +kernel
theorem good_209 : Good (rowAt 209) := by
  rw [row_209]
  unfold Good
  decide +kernel

def data_210 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 2)}, {(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)}, 6⟩
theorem entry_210_checked : entryAt 210 = entry_210 := by
  rw [entry_chunk_10 4 (by decide)]
  decide +kernel
theorem row_210 : rowAt 210 = data_210 := by
  rw [rowAt, dif_neg (by decide : ¬ 210 < 6), entry_210_checked]
  change forkRow [placeRow ⟨58, 2, 5, 4⟩ (rowAt 58), placeRow ⟨57, 0, 5, 4⟩ (rowAt 57), placeRow ⟨117, 1, 4, 5⟩ (rowAt 117)] = data_210
  rw [row_58, row_57, row_117]
  apply row_ext <;> decide +kernel
theorem entry_good_210 : EntryGood 210 := by
  unfold EntryGood
  rw [entry_210_checked]
  decide +kernel
theorem good_210 : Good (rowAt 210) := by
  rw [row_210]
  unfold Good
  decide +kernel

def data_211 : RowData := ⟨{(-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)}, 5⟩
theorem entry_211_checked : entryAt 211 = entry_211 := by
  rw [entry_chunk_10 5 (by decide)]
  decide +kernel
theorem row_211 : rowAt 211 = data_211 := by
  rw [rowAt, dif_neg (by decide : ¬ 211 < 6), entry_211_checked]
  change forkRow [placeRow ⟨49, 5, 5, 4⟩ (rowAt 49), placeRow ⟨6, 6, 0, 3⟩ (rowAt 6)] = data_211
  rw [row_49, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_211 : EntryGood 211 := by
  unfold EntryGood
  rw [entry_211_checked]
  decide +kernel
theorem good_211 : Good (rowAt 211) := by
  rw [row_211]
  unfold Good
  decide +kernel

def data_212 : RowData := ⟨{(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 1), (-1, -1), (0, -1)}, {(-4, 1), (-4, 2), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 2)}, 7⟩
theorem entry_212_checked : entryAt 212 = entry_212 := by
  rw [entry_chunk_10 6 (by decide)]
  decide +kernel
theorem row_212 : rowAt 212 = data_212 := by
  rw [rowAt, dif_neg (by decide : ¬ 212 < 6), entry_212_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨188, 0, 0, 5⟩ (rowAt 188)] = data_212
  rw [row_6, row_188]
  apply row_ext <;> decide +kernel
theorem entry_good_212 : EntryGood 212 := by
  unfold EntryGood
  rw [entry_212_checked]
  decide +kernel
theorem good_212 : Good (rowAt 212) := by
  rw [row_212]
  unfold Good
  decide +kernel

def data_213 : RowData := ⟨{(-1, -1), (-1, 0), (0, -1), (1, 0), (2, 0), (2, 1)}, {(-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (3, 1)}, 8⟩
theorem entry_213_checked : entryAt 213 = entry_213 := by
  rw [entry_chunk_10 7 (by decide)]
  decide +kernel
theorem row_213 : rowAt 213 = data_213 := by
  rw [rowAt, dif_neg (by decide : ¬ 213 < 6), entry_213_checked]
  change forkRow [placeRow ⟨6, 0, 7, 5⟩ (rowAt 6), placeRow ⟨191, 0, 3, 5⟩ (rowAt 191)] = data_213
  rw [row_6, row_191]
  apply row_ext <;> decide +kernel
theorem entry_good_213 : EntryGood 213 := by
  unfold EntryGood
  rw [entry_213_checked]
  decide +kernel
theorem good_213 : Good (rowAt 213) := by
  rw [row_213]
  unfold Good
  decide +kernel

def data_214 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1), (1, -3), (3, -2)}, {(-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 1), (1, 2), (1, 3), (2, -2), (3, -2)}, 7⟩
theorem entry_214_checked : entryAt 214 = entry_214 := by
  rw [entry_chunk_10 8 (by decide)]
  decide +kernel
theorem row_214 : rowAt 214 = data_214 := by
  rw [rowAt, dif_neg (by decide : ¬ 214 < 6), entry_214_checked]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨108, 3, 4, 5⟩ (rowAt 108), placeRow ⟨95, 0, 5, 2⟩ (rowAt 95)] = data_214
  rw [row_7, row_108, row_95]
  apply row_ext <;> decide +kernel
theorem entry_good_214 : EntryGood 214 := by
  unfold EntryGood
  rw [entry_214_checked]
  decide +kernel
theorem good_214 : Good (rowAt 214) := by
  rw [row_214]
  unfold Good
  decide +kernel

def data_215 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (0, 1)}, {(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, 0), (3, 0)}, 7⟩
theorem entry_215_checked : entryAt 215 = entry_215 := by
  rw [entry_chunk_10 9 (by decide)]
  decide +kernel
theorem row_215 : rowAt 215 = data_215 := by
  rw [rowAt, dif_neg (by decide : ¬ 215 < 6), entry_215_checked]
  change forkRow [placeRow ⟨107, 1, 4, 6⟩ (rowAt 107), placeRow ⟨24, 0, 5, 4⟩ (rowAt 24)] = data_215
  rw [row_107, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_215 : EntryGood 215 := by
  unfold EntryGood
  rw [entry_215_checked]
  decide +kernel
theorem good_215 : Good (rowAt 215) := by
  rw [row_215]
  unfold Good
  decide +kernel

def data_216 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, 1)}, 6⟩
theorem entry_216_checked : entryAt 216 = entry_216 := by
  rw [entry_chunk_10 10 (by decide)]
  decide +kernel
theorem row_216 : rowAt 216 = data_216 := by
  rw [rowAt, dif_neg (by decide : ¬ 216 < 6), entry_216_checked]
  change forkRow [placeRow ⟨7, 6, 0, 3⟩ (rowAt 7), placeRow ⟨155, 5, 5, 4⟩ (rowAt 155)] = data_216
  rw [row_7, row_155]
  apply row_ext <;> decide +kernel
theorem entry_good_216 : EntryGood 216 := by
  unfold EntryGood
  rw [entry_216_checked]
  decide +kernel
theorem good_216 : Good (rowAt 216) := by
  rw [row_216]
  unfold Good
  decide +kernel

def data_217 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 7⟩
theorem entry_217_checked : entryAt 217 = entry_217 := by
  rw [entry_chunk_10 11 (by decide)]
  decide +kernel
theorem row_217 : rowAt 217 = data_217 := by
  rw [rowAt, dif_neg (by decide : ¬ 217 < 6), entry_217_checked]
  change forkRow [placeRow ⟨111, 1, 1, 3⟩ (rowAt 111), placeRow ⟨55, 4, 0, 4⟩ (rowAt 55), placeRow ⟨64, 0, 1, 3⟩ (rowAt 64)] = data_217
  rw [row_111, row_55, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_217 : EntryGood 217 := by
  unfold EntryGood
  rw [entry_217_checked]
  decide +kernel
theorem good_217 : Good (rowAt 217) := by
  rw [row_217]
  unfold Good
  decide +kernel

def data_218 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (1, 2)}, {(-3, 0), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, 0)}, 6⟩
theorem entry_218_checked : entryAt 218 = entry_218 := by
  rw [entry_chunk_10 12 (by decide)]
  decide +kernel
theorem row_218 : rowAt 218 = data_218 := by
  rw [rowAt, dif_neg (by decide : ¬ 218 < 6), entry_218_checked]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (rowAt 0), placeRow ⟨182, 0, 2, 4⟩ (rowAt 182)] = data_218
  rw [row_0, row_182]
  apply row_ext <;> decide +kernel
theorem entry_good_218 : EntryGood 218 := by
  unfold EntryGood
  rw [entry_218_checked]
  decide +kernel
theorem good_218 : Good (rowAt 218) := by
  rw [row_218]
  unfold Good
  decide +kernel

def data_219 : RowData := ⟨{(-1, 0), (-1, 1), (-1, 2), (0, -1), (1, -1), (1, 0), (1, 1)}, {(-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1), (6, 1)}, 8⟩
theorem entry_219_checked : entryAt 219 = entry_219 := by
  rw [entry_chunk_10 13 (by decide)]
  decide +kernel
theorem row_219 : rowAt 219 = data_219 := by
  rw [rowAt, dif_neg (by decide : ¬ 219 < 6), entry_219_checked]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (rowAt 0), placeRow ⟨179, 2, 6, 4⟩ (rowAt 179)] = data_219
  rw [row_0, row_179]
  apply row_ext <;> decide +kernel
theorem entry_good_219 : EntryGood 219 := by
  unfold EntryGood
  rw [entry_219_checked]
  decide +kernel
theorem good_219 : Good (rowAt 219) := by
  rw [row_219]
  unfold Good
  decide +kernel

def data_220 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, 0), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)}, 7⟩
theorem entry_220_checked : entryAt 220 = entry_220 := by
  rw [entry_chunk_10 14 (by decide)]
  decide +kernel
theorem row_220 : rowAt 220 = data_220 := by
  rw [rowAt, dif_neg (by decide : ¬ 220 < 6), entry_220_checked]
  change forkRow [placeRow ⟨56, 4, 0, 4⟩ (rowAt 56), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨144, 2, 5, 4⟩ (rowAt 144), placeRow ⟨154, 6, 5, 4⟩ (rowAt 154), placeRow ⟨155, 1, 5, 4⟩ (rowAt 155)] = data_220
  rw [row_56, row_63, row_144, row_154, row_155]
  apply row_ext <;> decide +kernel
theorem entry_good_220 : EntryGood 220 := by
  unfold EntryGood
  rw [entry_220_checked]
  decide +kernel
theorem good_220 : Good (rowAt 220) := by
  rw [row_220]
  unfold Good
  decide +kernel

def data_221 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)}, 7⟩
theorem entry_221_checked : entryAt 221 = entry_221 := by
  rw [entry_chunk_10 15 (by decide)]
  decide +kernel
theorem row_221 : rowAt 221 = data_221 := by
  rw [rowAt, dif_neg (by decide : ¬ 221 < 6), entry_221_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨180, 5, 5, 4⟩ (rowAt 180)] = data_221
  rw [row_6, row_180]
  apply row_ext <;> decide +kernel
theorem entry_good_221 : EntryGood 221 := by
  unfold EntryGood
  rw [entry_221_checked]
  decide +kernel
theorem good_221 : Good (rowAt 221) := by
  rw [row_221]
  unfold Good
  decide +kernel

def data_222 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2)}, {(-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 6⟩
theorem entry_222_checked : entryAt 222 = entry_222 := by
  rw [entry_chunk_10 16 (by decide)]
  decide +kernel
theorem row_222 : rowAt 222 = data_222 := by
  rw [rowAt, dif_neg (by decide : ¬ 222 < 6), entry_222_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨158, 5, 5, 4⟩ (rowAt 158)] = data_222
  rw [row_6, row_158]
  apply row_ext <;> decide +kernel
theorem entry_good_222 : EntryGood 222 := by
  unfold EntryGood
  rw [entry_222_checked]
  decide +kernel
theorem good_222 : Good (rowAt 222) := by
  rw [row_222]
  unfold Good
  decide +kernel

def data_223 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, 0)}, {(-5, 0), (-4, 0), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)}, 7⟩
theorem entry_223_checked : entryAt 223 = entry_223 := by
  rw [entry_chunk_10 17 (by decide)]
  decide +kernel
theorem row_223 : rowAt 223 = data_223 := by
  rw [rowAt, dif_neg (by decide : ¬ 223 < 6), entry_223_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨135, 2, 5, 4⟩ (rowAt 135), placeRow ⟨128, 0, 3, 3⟩ (rowAt 128), placeRow ⟨111, 3, 4, 3⟩ (rowAt 111), placeRow ⟨127, 0, 5, 4⟩ (rowAt 127)] = data_223
  rw [row_63, row_135, row_128, row_111, row_127]
  apply row_ext <;> decide +kernel
theorem entry_good_223 : EntryGood 223 := by
  unfold EntryGood
  rw [entry_223_checked]
  decide +kernel
theorem good_223 : Good (rowAt 223) := by
  rw [row_223]
  unfold Good
  decide +kernel

#check row_223
def data_224 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (1, -2), (2, -2)}, {(-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 8⟩
theorem entry_224_checked : entryAt 224 = entry_224 := by
  rw [entry_chunk_10 18 (by decide)]
  decide +kernel
theorem row_224 : rowAt 224 = data_224 := by
  rw [rowAt, dif_neg (by decide : ¬ 224 < 6), entry_224_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨212, 0, 6, 3⟩ (rowAt 212)] = data_224
  rw [row_6, row_212]
  apply row_ext <;> decide +kernel
theorem entry_good_224 : EntryGood 224 := by
  unfold EntryGood
  rw [entry_224_checked]
  decide +kernel
theorem good_224 : Good (rowAt 224) := by
  rw [row_224]
  unfold Good
  decide +kernel

def data_225 : RowData := ⟨{(1, -2), (1, -1), (1, 0), (2, 0), (3, 0)}, {(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (2, 2), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 7⟩
theorem entry_225_checked : entryAt 225 = entry_225 := by
  rw [entry_chunk_10 19 (by decide)]
  decide +kernel
theorem row_225 : rowAt 225 = data_225 := by
  rw [rowAt, dif_neg (by decide : ¬ 225 < 6), entry_225_checked]
  change forkRow [placeRow ⟨111, 7, 7, 5⟩ (rowAt 111), placeRow ⟨61, 4, 4, 5⟩ (rowAt 61)] = data_225
  rw [row_111, row_61]
  apply row_ext <;> decide +kernel
theorem entry_good_225 : EntryGood 225 := by
  unfold EntryGood
  rw [entry_225_checked]
  decide +kernel
theorem good_225 : Good (rowAt 225) := by
  rw [row_225]
  unfold Good
  decide +kernel

def data_226 : RowData := ⟨{(-3, -1), (-3, 0), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 8⟩
theorem entry_226_checked : entryAt 226 = entry_226 := by
  rw [entry_chunk_11 0 (by decide)]
  decide +kernel
theorem row_226 : rowAt 226 = data_226 := by
  rw [rowAt, dif_neg (by decide : ¬ 226 < 6), entry_226_checked]
  change forkRow [placeRow ⟨10, 6, 0, 3⟩ (rowAt 10), placeRow ⟨203, 0, 5, 4⟩ (rowAt 203), placeRow ⟨33, 0, 2, 3⟩ (rowAt 33), placeRow ⟨193, 0, 2, 4⟩ (rowAt 193)] = data_226
  rw [row_10, row_203, row_33, row_193]
  apply row_ext <;> decide +kernel
theorem entry_good_226 : EntryGood 226 := by
  unfold EntryGood
  rw [entry_226_checked]
  decide +kernel
theorem good_226 : Good (rowAt 226) := by
  rw [row_226]
  unfold Good
  decide +kernel

def data_227 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (1, 0), (2, -2), (3, -2)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 8⟩
theorem entry_227_checked : entryAt 227 = entry_227 := by
  rw [entry_chunk_11 1 (by decide)]
  decide +kernel
theorem row_227 : rowAt 227 = data_227 := by
  rw [rowAt, dif_neg (by decide : ¬ 227 < 6), entry_227_checked]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (rowAt 6), placeRow ⟨212, 0, 7, 3⟩ (rowAt 212)] = data_227
  rw [row_6, row_212]
  apply row_ext <;> decide +kernel
theorem entry_good_227 : EntryGood 227 := by
  unfold EntryGood
  rw [entry_227_checked]
  decide +kernel
theorem good_227 : Good (rowAt 227) := by
  rw [row_227]
  unfold Good
  decide +kernel

def data_228 : RowData := ⟨{(1, -2), (1, -1), (1, 0), (1, 1), (1, 2)}, {(-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (3, 1), (4, 1)}, 6⟩
theorem entry_228_checked : entryAt 228 = entry_228 := by
  rw [entry_chunk_11 2 (by decide)]
  decide +kernel
theorem row_228 : rowAt 228 = data_228 := by
  rw [rowAt, dif_neg (by decide : ¬ 228 < 6), entry_228_checked]
  change forkRow [placeRow ⟨82, 0, 6, 5⟩ (rowAt 82), placeRow ⟨68, 3, 5, 7⟩ (rowAt 68)] = data_228
  rw [row_82, row_68]
  apply row_ext <;> decide +kernel
theorem entry_good_228 : EntryGood 228 := by
  unfold EntryGood
  rw [entry_228_checked]
  decide +kernel
theorem good_228 : Good (rowAt 228) := by
  rw [row_228]
  unfold Good
  decide +kernel

def data_229 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (4, -1)}, 7⟩
theorem entry_229_checked : entryAt 229 = entry_229 := by
  rw [entry_chunk_11 3 (by decide)]
  decide +kernel
theorem row_229 : rowAt 229 = data_229 := by
  rw [rowAt, dif_neg (by decide : ¬ 229 < 6), entry_229_checked]
  change forkRow [placeRow ⟨171, 0, 7, 3⟩ (rowAt 171), placeRow ⟨45, 1, 4, 5⟩ (rowAt 45), placeRow ⟨46, 3, 4, 5⟩ (rowAt 46)] = data_229
  rw [row_171, row_45, row_46]
  apply row_ext <;> decide +kernel
theorem entry_good_229 : EntryGood 229 := by
  unfold EntryGood
  rw [entry_229_checked]
  decide +kernel
theorem good_229 : Good (rowAt 229) := by
  rw [row_229]
  unfold Good
  decide +kernel

def data_230 : RowData := ⟨{(0, 1), (2, 0), (2, 1), (3, 1)}, {(-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0), (7, 2)}, 8⟩
theorem entry_230_checked : entryAt 230 = entry_230 := by
  rw [entry_chunk_11 4 (by decide)]
  decide +kernel
theorem row_230 : rowAt 230 = data_230 := by
  rw [rowAt, dif_neg (by decide : ¬ 230 < 6), entry_230_checked]
  change forkRow [placeRow ⟨10, 6, 3, 4⟩ (rowAt 10), placeRow ⟨193, 0, 5, 5⟩ (rowAt 193), placeRow ⟨203, 0, 8, 5⟩ (rowAt 203), placeRow ⟨33, 0, 5, 4⟩ (rowAt 33)] = data_230
  rw [row_10, row_193, row_203, row_33]
  apply row_ext <;> decide +kernel
theorem entry_good_230 : EntryGood 230 := by
  unfold EntryGood
  rw [entry_230_checked]
  decide +kernel
theorem good_230 : Good (rowAt 230) := by
  rw [row_230]
  unfold Good
  decide +kernel

def data_231 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2)}, {(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 7⟩
theorem entry_231_checked : entryAt 231 = entry_231 := by
  rw [entry_chunk_11 5 (by decide)]
  decide +kernel
theorem row_231 : rowAt 231 = data_231 := by
  rw [rowAt, dif_neg (by decide : ¬ 231 < 6), entry_231_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨222, 0, 6, 4⟩ (rowAt 222)] = data_231
  rw [row_6, row_222]
  apply row_ext <;> decide +kernel
theorem entry_good_231 : EntryGood 231 := by
  unfold EntryGood
  rw [entry_231_checked]
  decide +kernel
theorem good_231 : Good (rowAt 231) := by
  rw [row_231]
  unfold Good
  decide +kernel

def data_232 : RowData := ⟨{(-2, 1), (-1, -1), (-1, 1), (0, -1), (0, 1)}, {(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (3, 0)}, 7⟩
theorem entry_232_checked : entryAt 232 = entry_232 := by
  rw [entry_chunk_11 6 (by decide)]
  decide +kernel
theorem row_232 : rowAt 232 = data_232 := by
  rw [rowAt, dif_neg (by decide : ¬ 232 < 6), entry_232_checked]
  change forkRow [placeRow ⟨24, 2, 5, 4⟩ (rowAt 24), placeRow ⟨107, 1, 4, 6⟩ (rowAt 107)] = data_232
  rw [row_24, row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_232 : EntryGood 232 := by
  unfold EntryGood
  rw [entry_232_checked]
  decide +kernel
theorem good_232 : Good (rowAt 232) := by
  rw [row_232]
  unfold Good
  decide +kernel

def data_233 : RowData := ⟨{(-1, -2), (0, -2), (0, -1), (1, -2), (2, -2), (2, -1), (2, 1)}, {(-2, -3), (-1, -3), (-1, -2), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1), (3, 2), (4, 1), (5, 1)}, 6⟩
theorem entry_233_checked : entryAt 233 = entry_233 := by
  rw [entry_chunk_11 7 (by decide)]
  decide +kernel
theorem row_233 : rowAt 233 = data_233 := by
  rw [rowAt, dif_neg (by decide : ¬ 233 < 6), entry_233_checked]
  change forkRow [placeRow ⟨32, 3, 3, 1⟩ (rowAt 32), placeRow ⟨133, 0, 6, 4⟩ (rowAt 133)] = data_233
  rw [row_32, row_133]
  apply row_ext <;> decide +kernel
theorem entry_good_233 : EntryGood 233 := by
  unfold EntryGood
  rw [entry_233_checked]
  decide +kernel
theorem good_233 : Good (rowAt 233) := by
  rw [row_233]
  unfold Good
  decide +kernel

def data_234 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (3, -1)}, 7⟩
theorem entry_234_checked : entryAt 234 = entry_234 := by
  rw [entry_chunk_11 8 (by decide)]
  decide +kernel
theorem row_234 : rowAt 234 = data_234 := by
  rw [rowAt, dif_neg (by decide : ¬ 234 < 6), entry_234_checked]
  change forkRow [placeRow ⟨180, 4, 4, 5⟩ (rowAt 180), placeRow ⟨37, 0, 3, 4⟩ (rowAt 37), placeRow ⟨129, 0, 5, 3⟩ (rowAt 129), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63)] = data_234
  rw [row_180, row_37, row_129, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_234 : EntryGood 234 := by
  unfold EntryGood
  rw [entry_234_checked]
  decide +kernel
theorem good_234 : Good (rowAt 234) := by
  rw [row_234]
  unfold Good
  decide +kernel

def data_235 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1), (1, 0), (3, 0)}, {(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 7⟩
theorem entry_235_checked : entryAt 235 = entry_235 := by
  rw [entry_chunk_11 9 (by decide)]
  decide +kernel
theorem row_235 : rowAt 235 = data_235 := by
  rw [rowAt, dif_neg (by decide : ¬ 235 < 6), entry_235_checked]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨110, 0, 6, 4⟩ (rowAt 110), placeRow ⟨70, 0, 3, 5⟩ (rowAt 70)] = data_235
  rw [row_7, row_110, row_70]
  apply row_ext <;> decide +kernel
theorem entry_good_235 : EntryGood 235 := by
  unfold EntryGood
  rw [entry_235_checked]
  decide +kernel
theorem good_235 : Good (rowAt 235) := by
  rw [row_235]
  unfold Good
  decide +kernel

def data_236 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (2, 0), (3, 0)}, 6⟩
theorem entry_236_checked : entryAt 236 = entry_236 := by
  rw [entry_chunk_11 10 (by decide)]
  decide +kernel
theorem row_236 : rowAt 236 = data_236 := by
  rw [rowAt, dif_neg (by decide : ¬ 236 < 6), entry_236_checked]
  change forkRow [placeRow ⟨38, 1, 4, 5⟩ (rowAt 38), placeRow ⟨122, 7, 3, 4⟩ (rowAt 122), placeRow ⟨181, 0, 2, 3⟩ (rowAt 181), placeRow ⟨30, 1, 4, 3⟩ (rowAt 30)] = data_236
  rw [row_38, row_122, row_181, row_30]
  apply row_ext <;> decide +kernel
theorem entry_good_236 : EntryGood 236 := by
  unfold EntryGood
  rw [entry_236_checked]
  decide +kernel
theorem good_236 : Good (rowAt 236) := by
  rw [row_236]
  unfold Good
  decide +kernel

def data_237 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, 0)}, {(-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 7⟩
theorem entry_237_checked : entryAt 237 = entry_237 := by
  rw [entry_chunk_11 11 (by decide)]
  decide +kernel
theorem row_237 : rowAt 237 = data_237 := by
  rw [rowAt, dif_neg (by decide : ¬ 237 < 6), entry_237_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨172, 0, 7, 4⟩ (rowAt 172)] = data_237
  rw [row_6, row_172]
  apply row_ext <;> decide +kernel
theorem entry_good_237 : EntryGood 237 := by
  unfold EntryGood
  rw [entry_237_checked]
  decide +kernel
theorem good_237 : Good (rowAt 237) := by
  rw [row_237]
  unfold Good
  decide +kernel

def data_238 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, 0)}, {(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 7⟩
theorem entry_238_checked : entryAt 238 = entry_238 := by
  rw [entry_chunk_11 12 (by decide)]
  decide +kernel
theorem row_238 : rowAt 238 = data_238 := by
  rw [rowAt, dif_neg (by decide : ¬ 238 < 6), entry_238_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨178, 5, 7, 4⟩ (rowAt 178)] = data_238
  rw [row_6, row_178]
  apply row_ext <;> decide +kernel
theorem entry_good_238 : EntryGood 238 := by
  unfold EntryGood
  rw [entry_238_checked]
  decide +kernel
theorem good_238 : Good (rowAt 238) := by
  rw [row_238]
  unfold Good
  decide +kernel

def data_239 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0), (0, -1), (1, -1), (2, -1)}, {(-4, 1), (-3, 1), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (3, -1)}, 7⟩
theorem entry_239_checked : entryAt 239 = entry_239 := by
  rw [entry_chunk_11 13 (by decide)]
  decide +kernel
theorem row_239 : rowAt 239 = data_239 := by
  rw [rowAt, dif_neg (by decide : ¬ 239 < 6), entry_239_checked]
  change forkRow [placeRow ⟨0, 4, 7, 3⟩ (rowAt 0), placeRow ⟨174, 4, 3, 5⟩ (rowAt 174)] = data_239
  rw [row_0, row_174]
  apply row_ext <;> decide +kernel
theorem entry_good_239 : EntryGood 239 := by
  unfold EntryGood
  rw [entry_239_checked]
  decide +kernel
theorem good_239 : Good (rowAt 239) := by
  rw [row_239]
  unfold Good
  decide +kernel

def data_240 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 8⟩
theorem entry_240_checked : entryAt 240 = entry_240 := by
  rw [entry_chunk_11 14 (by decide)]
  decide +kernel
theorem row_240 : rowAt 240 = data_240 := by
  rw [rowAt, dif_neg (by decide : ¬ 240 < 6), entry_240_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨237, 0, 2, 4⟩ (rowAt 237)] = data_240
  rw [row_6, row_237]
  apply row_ext <;> decide +kernel
theorem entry_good_240 : EntryGood 240 := by
  unfold EntryGood
  rw [entry_240_checked]
  decide +kernel
theorem good_240 : Good (rowAt 240) := by
  rw [row_240]
  unfold Good
  decide +kernel

def data_241 : RowData := ⟨{(-3, 0), (-2, 0), (-1, -2), (-1, -1), (-1, 0)}, {(-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)}, 7⟩
theorem entry_241_checked : entryAt 241 = entry_241 := by
  rw [entry_chunk_11 15 (by decide)]
  decide +kernel
theorem row_241 : rowAt 241 = data_241 := by
  rw [rowAt, dif_neg (by decide : ¬ 241 < 6), entry_241_checked]
  change forkRow [placeRow ⟨131, 1, 5, 4⟩ (rowAt 131), placeRow ⟨159, 1, 5, 4⟩ (rowAt 159), placeRow ⟨61, 0, 4, 5⟩ (rowAt 61)] = data_241
  rw [row_131, row_159, row_61]
  apply row_ext <;> decide +kernel
theorem entry_good_241 : EntryGood 241 := by
  unfold EntryGood
  rw [entry_241_checked]
  decide +kernel
theorem good_241 : Good (rowAt 241) := by
  rw [row_241]
  unfold Good
  decide +kernel

def data_242 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-3, 0), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1)}, 8⟩
theorem entry_242_checked : entryAt 242 = entry_242 := by
  rw [entry_chunk_11 16 (by decide)]
  decide +kernel
theorem row_242 : rowAt 242 = data_242 := by
  rw [rowAt, dif_neg (by decide : ¬ 242 < 6), entry_242_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨190, 0, 5, 4⟩ (rowAt 190)] = data_242
  rw [row_6, row_190]
  apply row_ext <;> decide +kernel
theorem entry_good_242 : EntryGood 242 := by
  unfold EntryGood
  rw [entry_242_checked]
  decide +kernel
theorem good_242 : Good (rowAt 242) := by
  rw [row_242]
  unfold Good
  decide +kernel

def data_243 : RowData := ⟨{(-3, -1), (-2, -1), (-2, 0), (-1, -1), (0, -1), (0, 2)}, {(-4, -2), (-3, -2), (-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (3, 2)}, 7⟩
theorem entry_243_checked : entryAt 243 = entry_243 := by
  rw [entry_chunk_11 17 (by decide)]
  decide +kernel
theorem row_243 : rowAt 243 = data_243 := by
  rw [rowAt, dif_neg (by decide : ¬ 243 < 6), entry_243_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨233, 0, 2, 5⟩ (rowAt 233)] = data_243
  rw [row_6, row_233]
  apply row_ext <;> decide +kernel
theorem entry_good_243 : EntryGood 243 := by
  unfold EntryGood
  rw [entry_243_checked]
  decide +kernel
theorem good_243 : Good (rowAt 243) := by
  rw [row_243]
  unfold Good
  decide +kernel

def data_244 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, 0)}, {(-5, 1), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 7⟩
theorem entry_244_checked : entryAt 244 = entry_244 := by
  rw [entry_chunk_11 18 (by decide)]
  decide +kernel
theorem row_244 : rowAt 244 = data_244 := by
  rw [rowAt, dif_neg (by decide : ¬ 244 < 6), entry_244_checked]
  change forkRow [placeRow ⟨99, 4, 2, 5⟩ (rowAt 99), placeRow ⟨99, 0, 4, 5⟩ (rowAt 99), placeRow ⟨11, 7, 3, 3⟩ (rowAt 11), placeRow ⟨173, 2, 5, 4⟩ (rowAt 173)] = data_244
  rw [row_99, row_11, row_173]
  apply row_ext <;> decide +kernel
theorem entry_good_244 : EntryGood 244 := by
  unfold EntryGood
  rw [entry_244_checked]
  decide +kernel
theorem good_244 : Good (rowAt 244) := by
  rw [row_244]
  unfold Good
  decide +kernel

def data_245 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 8⟩
theorem entry_245_checked : entryAt 245 = entry_245 := by
  rw [entry_chunk_11 19 (by decide)]
  decide +kernel
theorem row_245 : rowAt 245 = data_245 := by
  rw [rowAt, dif_neg (by decide : ¬ 245 < 6), entry_245_checked]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (rowAt 64), placeRow ⟨175, 4, 0, 4⟩ (rowAt 175), placeRow ⟨143, 6, 4, 5⟩ (rowAt 143), placeRow ⟨186, 6, 0, 4⟩ (rowAt 186)] = data_245
  rw [row_64, row_175, row_143, row_186]
  apply row_ext <;> decide +kernel
theorem entry_good_245 : EntryGood 245 := by
  unfold EntryGood
  rw [entry_245_checked]
  decide +kernel
theorem good_245 : Good (rowAt 245) := by
  rw [row_245]
  unfold Good
  decide +kernel

def data_246 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)}, 8⟩
theorem entry_246_checked : entryAt 246 = entry_246 := by
  rw [entry_chunk_12 0 (by decide)]
  decide +kernel
theorem row_246 : rowAt 246 = data_246 := by
  rw [rowAt, dif_neg (by decide : ¬ 246 < 6), entry_246_checked]
  change forkRow [placeRow ⟨64, 6, 4, 5⟩ (rowAt 64), placeRow ⟨175, 2, 5, 4⟩ (rowAt 175), placeRow ⟨186, 0, 5, 4⟩ (rowAt 186), placeRow ⟨143, 0, 1, 3⟩ (rowAt 143)] = data_246
  rw [row_64, row_175, row_186, row_143]
  apply row_ext <;> decide +kernel
theorem entry_good_246 : EntryGood 246 := by
  unfold EntryGood
  rw [entry_246_checked]
  decide +kernel
theorem good_246 : Good (rowAt 246) := by
  rw [row_246]
  unfold Good
  decide +kernel

def data_247 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (4, 0)}, 8⟩
theorem entry_247_checked : entryAt 247 = entry_247 := by
  rw [entry_chunk_12 1 (by decide)]
  decide +kernel
theorem row_247 : rowAt 247 = data_247 := by
  rw [rowAt, dif_neg (by decide : ¬ 247 < 6), entry_247_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨229, 0, 4, 5⟩ (rowAt 229)] = data_247
  rw [row_6, row_229]
  apply row_ext <;> decide +kernel
theorem entry_good_247 : EntryGood 247 := by
  unfold EntryGood
  rw [entry_247_checked]
  decide +kernel
theorem good_247 : Good (rowAt 247) := by
  rw [row_247]
  unfold Good
  decide +kernel

def data_248 : RowData := ⟨{(-1, 0), (1, 0), (2, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)}, 8⟩
theorem entry_248_checked : entryAt 248 = entry_248 := by
  rw [entry_chunk_12 2 (by decide)]
  decide +kernel
theorem row_248 : rowAt 248 = data_248 := by
  rw [rowAt, dif_neg (by decide : ¬ 248 < 6), entry_248_checked]
  change forkRow [placeRow ⟨186, 0, 7, 4⟩ (rowAt 186), placeRow ⟨143, 0, 3, 3⟩ (rowAt 143), placeRow ⟨175, 2, 7, 4⟩ (rowAt 175), placeRow ⟨64, 6, 6, 5⟩ (rowAt 64)] = data_248
  rw [row_186, row_143, row_175, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_248 : EntryGood 248 := by
  unfold EntryGood
  rw [entry_248_checked]
  decide +kernel
theorem good_248 : Good (rowAt 248) := by
  rw [row_248]
  unfold Good
  decide +kernel

def data_249 : RowData := ⟨{(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, -1)}, {(-3, 0), (-2, -2), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (2, -3), (2, -1), (3, -3)}, 8⟩
theorem entry_249_checked : entryAt 249 = entry_249 := by
  rw [entry_chunk_12 3 (by decide)]
  decide +kernel
theorem row_249 : rowAt 249 = data_249 := by
  rw [rowAt, dif_neg (by decide : ¬ 249 < 6), entry_249_checked]
  change forkRow [placeRow ⟨0, 7, 4, 5⟩ (rowAt 0), placeRow ⟨225, 1, 4, 1⟩ (rowAt 225)] = data_249
  rw [row_0, row_225]
  apply row_ext <;> decide +kernel
theorem entry_good_249 : EntryGood 249 := by
  unfold EntryGood
  rw [entry_249_checked]
  decide +kernel
theorem good_249 : Good (rowAt 249) := by
  rw [row_249]
  unfold Good
  decide +kernel

def data_250 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2)}, {(-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 8⟩
theorem entry_250_checked : entryAt 250 = entry_250 := by
  rw [entry_chunk_12 4 (by decide)]
  decide +kernel
theorem row_250 : rowAt 250 = data_250 := by
  rw [rowAt, dif_neg (by decide : ¬ 250 < 6), entry_250_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨238, 0, 2, 4⟩ (rowAt 238)] = data_250
  rw [row_6, row_238]
  apply row_ext <;> decide +kernel
theorem entry_good_250 : EntryGood 250 := by
  unfold EntryGood
  rw [entry_250_checked]
  decide +kernel
theorem good_250 : Good (rowAt 250) := by
  rw [row_250]
  unfold Good
  decide +kernel

def data_251 : RowData := ⟨{(-3, 1), (-2, 1), (-1, 1), (0, 1), (0, 2)}, {(-4, 1), (-3, 1), (-2, 1), (-2, 2), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 3), (1, 4), (1, 5), (2, 3), (3, 3)}, 8⟩
theorem entry_251_checked : entryAt 251 = entry_251 := by
  rw [entry_chunk_12 5 (by decide)]
  decide +kernel
theorem row_251 : rowAt 251 = data_251 := by
  rw [rowAt, dif_neg (by decide : ¬ 251 < 6), entry_251_checked]
  change forkRow [placeRow ⟨6, 2, 5, 4⟩ (rowAt 6), placeRow ⟨239, 4, 3, 6⟩ (rowAt 239)] = data_251
  rw [row_6, row_239]
  apply row_ext <;> decide +kernel
theorem entry_good_251 : EntryGood 251 := by
  unfold EntryGood
  rw [entry_251_checked]
  decide +kernel
theorem good_251 : Good (rowAt 251) := by
  rw [row_251]
  unfold Good
  decide +kernel

def data_252 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, 0), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)}, 7⟩
theorem entry_252_checked : entryAt 252 = entry_252 := by
  rw [entry_chunk_12 6 (by decide)]
  decide +kernel
theorem row_252 : rowAt 252 = data_252 := by
  rw [rowAt, dif_neg (by decide : ¬ 252 < 6), entry_252_checked]
  change forkRow [placeRow ⟨111, 3, 4, 3⟩ (rowAt 111), placeRow ⟨154, 6, 5, 4⟩ (rowAt 154), placeRow ⟨144, 2, 5, 4⟩ (rowAt 144), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨155, 1, 5, 4⟩ (rowAt 155)] = data_252
  rw [row_111, row_154, row_144, row_63, row_155]
  apply row_ext <;> decide +kernel
theorem entry_good_252 : EntryGood 252 := by
  unfold EntryGood
  rw [entry_252_checked]
  decide +kernel
theorem good_252 : Good (rowAt 252) := by
  rw [row_252]
  unfold Good
  decide +kernel

def data_253 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3), (2, 0)}, {(-2, -4), (-1, -4), (-1, -3), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (4, -1), (5, -1)}, 7⟩
theorem entry_253_checked : entryAt 253 = entry_253 := by
  rw [entry_chunk_12 7 (by decide)]
  decide +kernel
theorem row_253 : rowAt 253 = data_253 := by
  rw [rowAt, dif_neg (by decide : ¬ 253 < 6), entry_253_checked]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (rowAt 29), placeRow ⟨177, 1, 6, 2⟩ (rowAt 177)] = data_253
  rw [row_29, row_177]
  apply row_ext <;> decide +kernel
theorem entry_good_253 : EntryGood 253 := by
  unfold EntryGood
  rw [entry_253_checked]
  decide +kernel
theorem good_253 : Good (rowAt 253) := by
  rw [row_253]
  unfold Good
  decide +kernel

def data_254 : RowData := ⟨{(0, -2), (1, 1), (2, 1), (3, 1)}, {(-2, 2), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 1), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)}, 7⟩
theorem entry_254_checked : entryAt 254 = entry_254 := by
  rw [entry_chunk_12 8 (by decide)]
  decide +kernel
theorem row_254 : rowAt 254 = data_254 := by
  rw [rowAt, dif_neg (by decide : ¬ 254 < 6), entry_254_checked]
  change forkRow [placeRow ⟨96, 7, 4, 5⟩ (rowAt 96), placeRow ⟨108, 0, 8, 5⟩ (rowAt 108)] = data_254
  rw [row_96, row_108]
  apply row_ext <;> decide +kernel
theorem entry_good_254 : EntryGood 254 := by
  unfold EntryGood
  rw [entry_254_checked]
  decide +kernel
theorem good_254 : Good (rowAt 254) := by
  rw [row_254]
  unfold Good
  decide +kernel

def data_255 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1), (3, 0)}, {(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)}, 9⟩
theorem entry_255_checked : entryAt 255 = entry_255 := by
  rw [entry_chunk_12 9 (by decide)]
  decide +kernel
theorem row_255 : rowAt 255 = data_255 := by
  rw [rowAt, dif_neg (by decide : ¬ 255 < 6), entry_255_checked]
  change forkRow [placeRow ⟨69, 0, 3, 3⟩ (rowAt 69), placeRow ⟨205, 0, 5, 5⟩ (rowAt 205), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7)] = data_255
  rw [row_69, row_205, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_255 : EntryGood 255 := by
  unfold EntryGood
  rw [entry_255_checked]
  decide +kernel
theorem good_255 : Good (rowAt 255) := by
  rw [row_255]
  unfold Good
  decide +kernel

#check row_255
def data_256 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3), (1, -2)}, {(-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 8⟩
theorem entry_256_checked : entryAt 256 = entry_256 := by
  rw [entry_chunk_12 10 (by decide)]
  decide +kernel
theorem row_256 : rowAt 256 = data_256 := by
  rw [rowAt, dif_neg (by decide : ¬ 256 < 6), entry_256_checked]
  change forkRow [placeRow ⟨0, 5, 4, 5⟩ (rowAt 0), placeRow ⟨231, 0, 3, 4⟩ (rowAt 231)] = data_256
  rw [row_0, row_231]
  apply row_ext <;> decide +kernel
theorem entry_good_256 : EntryGood 256 := by
  unfold EntryGood
  rw [entry_256_checked]
  decide +kernel
theorem good_256 : Good (rowAt 256) := by
  rw [row_256]
  unfold Good
  decide +kernel

def data_257 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, 1), (3, 1)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)}, 8⟩
theorem entry_257_checked : entryAt 257 = entry_257 := by
  rw [entry_chunk_12 11 (by decide)]
  decide +kernel
theorem row_257 : rowAt 257 = data_257 := by
  rw [rowAt, dif_neg (by decide : ¬ 257 < 6), entry_257_checked]
  change forkRow [placeRow ⟨4, 1, 5, 4⟩ (rowAt 4), placeRow ⟨235, 0, 4, 5⟩ (rowAt 235)] = data_257
  rw [row_4, row_235]
  apply row_ext <;> decide +kernel
theorem entry_good_257 : EntryGood 257 := by
  unfold EntryGood
  rw [entry_257_checked]
  decide +kernel
theorem good_257 : Good (rowAt 257) := by
  rw [row_257]
  unfold Good
  decide +kernel

def data_258 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (1, 1), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 1), (1, 2), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)}, 9⟩
theorem entry_258_checked : entryAt 258 = entry_258 := by
  rw [entry_chunk_12 12 (by decide)]
  decide +kernel
theorem row_258 : rowAt 258 = data_258 := by
  rw [rowAt, dif_neg (by decide : ¬ 258 < 6), entry_258_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨227, 0, 4, 5⟩ (rowAt 227)] = data_258
  rw [row_6, row_227]
  apply row_ext <;> decide +kernel
theorem entry_good_258 : EntryGood 258 := by
  unfold EntryGood
  rw [entry_258_checked]
  decide +kernel
theorem good_258 : Good (rowAt 258) := by
  rw [row_258]
  unfold Good
  decide +kernel

def data_259 : RowData := ⟨{(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)}, {(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3)}, 8⟩
theorem entry_259_checked : entryAt 259 = entry_259 := by
  rw [entry_chunk_12 13 (by decide)]
  decide +kernel
theorem row_259 : rowAt 259 = data_259 := by
  rw [rowAt, dif_neg (by decide : ¬ 259 < 6), entry_259_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨231, 1, 7, 2⟩ (rowAt 231)] = data_259
  rw [row_6, row_231]
  apply row_ext <;> decide +kernel
theorem entry_good_259 : EntryGood 259 := by
  unfold EntryGood
  rw [entry_259_checked]
  decide +kernel
theorem good_259 : Good (rowAt 259) := by
  rw [row_259]
  unfold Good
  decide +kernel

def data_260 : RowData := ⟨{(0, -2), (0, -1), (0, 1), (1, -2), (1, -1)}, {(-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)}, 8⟩
theorem entry_260_checked : entryAt 260 = entry_260 := by
  rw [entry_chunk_12 14 (by decide)]
  decide +kernel
theorem row_260 : rowAt 260 = data_260 := by
  rw [rowAt, dif_neg (by decide : ¬ 260 < 6), entry_260_checked]
  change forkRow [placeRow ⟨0, 5, 4, 6⟩ (rowAt 0), placeRow ⟨231, 0, 3, 5⟩ (rowAt 231)] = data_260
  rw [row_0, row_231]
  apply row_ext <;> decide +kernel
theorem entry_good_260 : EntryGood 260 := by
  unfold EntryGood
  rw [entry_260_checked]
  decide +kernel
theorem good_260 : Good (rowAt 260) := by
  rw [row_260]
  unfold Good
  decide +kernel

def data_261 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0)}, {(-1, 0), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, 0), (5, 1)}, 9⟩
theorem entry_261_checked : entryAt 261 = entry_261 := by
  rw [entry_chunk_12 15 (by decide)]
  decide +kernel
theorem row_261 : rowAt 261 = data_261 := by
  rw [rowAt, dif_neg (by decide : ¬ 261 < 6), entry_261_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨242, 0, 6, 4⟩ (rowAt 242)] = data_261
  rw [row_6, row_242]
  apply row_ext <;> decide +kernel
theorem entry_good_261 : EntryGood 261 := by
  unfold EntryGood
  rw [entry_261_checked]
  decide +kernel
theorem good_261 : Good (rowAt 261) := by
  rw [row_261]
  unfold Good
  decide +kernel

def data_262 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (0, -1), (1, 0), (1, 1), (1, 2)}, {(-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1)}, 9⟩
theorem entry_262_checked : entryAt 262 = entry_262 := by
  rw [entry_chunk_12 16 (by decide)]
  decide +kernel
theorem row_262 : rowAt 262 = data_262 := by
  rw [rowAt, dif_neg (by decide : ¬ 262 < 6), entry_262_checked]
  change forkRow [placeRow ⟨0, 7, 5, 7⟩ (rowAt 0), placeRow ⟨213, 0, 3, 4⟩ (rowAt 213)] = data_262
  rw [row_0, row_213]
  apply row_ext <;> decide +kernel
theorem entry_good_262 : EntryGood 262 := by
  unfold EntryGood
  rw [entry_262_checked]
  decide +kernel
theorem good_262 : Good (rowAt 262) := by
  rw [row_262]
  unfold Good
  decide +kernel

def data_263 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-6, -1), (-5, -1), (-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)}, 8⟩
theorem entry_263_checked : entryAt 263 = entry_263 := by
  rw [entry_chunk_12 17 (by decide)]
  decide +kernel
theorem row_263 : rowAt 263 = data_263 := by
  rw [rowAt, dif_neg (by decide : ¬ 263 < 6), entry_263_checked]
  change forkRow [placeRow ⟨144, 6, 0, 4⟩ (rowAt 144), placeRow ⟨143, 0, 1, 3⟩ (rowAt 143), placeRow ⟨175, 0, 5, 4⟩ (rowAt 175), placeRow ⟨55, 6, 0, 4⟩ (rowAt 55)] = data_263
  rw [row_144, row_143, row_175, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_263 : EntryGood 263 := by
  unfold EntryGood
  rw [entry_263_checked]
  decide +kernel
theorem good_263 : Good (rowAt 263) := by
  rw [row_263]
  unfold Good
  decide +kernel

def data_264 : RowData := ⟨{(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)}, {(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3)}, 9⟩
theorem entry_264_checked : entryAt 264 = entry_264 := by
  rw [entry_chunk_12 18 (by decide)]
  decide +kernel
theorem row_264 : rowAt 264 = data_264 := by
  rw [rowAt, dif_neg (by decide : ¬ 264 < 6), entry_264_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨250, 1, 7, 4⟩ (rowAt 250)] = data_264
  rw [row_6, row_250]
  apply row_ext <;> decide +kernel
theorem entry_good_264 : EntryGood 264 := by
  unfold EntryGood
  rw [entry_264_checked]
  decide +kernel
theorem good_264 : Good (rowAt 264) := by
  rw [row_264]
  unfold Good
  decide +kernel

def data_265 : RowData := ⟨{(0, 1), (1, 1), (2, 1), (3, 1)}, {(-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (4, 2)}, 9⟩
theorem entry_265_checked : entryAt 265 = entry_265 := by
  rw [entry_chunk_12 19 (by decide)]
  decide +kernel
theorem row_265 : rowAt 265 = data_265 := by
  rw [rowAt, dif_neg (by decide : ¬ 265 < 6), entry_265_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨247, 0, 4, 6⟩ (rowAt 247)] = data_265
  rw [row_6, row_247]
  apply row_ext <;> decide +kernel
theorem entry_good_265 : EntryGood 265 := by
  unfold EntryGood
  rw [entry_265_checked]
  decide +kernel
theorem good_265 : Good (rowAt 265) := by
  rw [row_265]
  unfold Good
  decide +kernel

def data_266 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1)}, {(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)}, 9⟩
theorem entry_266_checked : entryAt 266 = entry_266 := by
  rw [entry_chunk_13 0 (by decide)]
  decide +kernel
theorem row_266 : rowAt 266 = data_266 := by
  rw [rowAt, dif_neg (by decide : ¬ 266 < 6), entry_266_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨242, 0, 5, 4⟩ (rowAt 242)] = data_266
  rw [row_6, row_242]
  apply row_ext <;> decide +kernel
theorem entry_good_266 : EntryGood 266 := by
  unfold EntryGood
  rw [entry_266_checked]
  decide +kernel
theorem good_266 : Good (rowAt 266) := by
  rw [row_266]
  unfold Good
  decide +kernel

def data_267 : RowData := ⟨{(-2, 0), (-1, 0), (1, 0)}, {(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1)}, 8⟩
theorem entry_267_checked : entryAt 267 = entry_267 := by
  rw [entry_chunk_13 1 (by decide)]
  decide +kernel
theorem row_267 : rowAt 267 = data_267 := by
  rw [rowAt, dif_neg (by decide : ¬ 267 < 6), entry_267_checked]
  change forkRow [placeRow ⟨175, 4, 1, 4⟩ (rowAt 175), placeRow ⟨144, 2, 6, 4⟩ (rowAt 144), placeRow ⟨55, 2, 6, 4⟩ (rowAt 55), placeRow ⟨143, 4, 5, 3⟩ (rowAt 143)] = data_267
  rw [row_175, row_144, row_55, row_143]
  apply row_ext <;> decide +kernel
theorem entry_good_267 : EntryGood 267 := by
  unfold EntryGood
  rw [entry_267_checked]
  decide +kernel
theorem good_267 : Good (rowAt 267) := by
  rw [row_267]
  unfold Good
  decide +kernel

def data_268 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (0, -1)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (3, 1)}, 9⟩
theorem entry_268_checked : entryAt 268 = entry_268 := by
  rw [entry_chunk_13 2 (by decide)]
  decide +kernel
theorem row_268 : rowAt 268 = data_268 := by
  rw [rowAt, dif_neg (by decide : ¬ 268 < 6), entry_268_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨251, 0, 4, 2⟩ (rowAt 251)] = data_268
  rw [row_6, row_251]
  apply row_ext <;> decide +kernel
theorem entry_good_268 : EntryGood 268 := by
  unfold EntryGood
  rw [entry_268_checked]
  decide +kernel
theorem good_268 : Good (rowAt 268) := by
  rw [row_268]
  unfold Good
  decide +kernel

def data_269 : RowData := ⟨{(-1, 1), (-1, 3), (0, 1), (1, 1), (2, 1)}, {(-2, 2), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)}, 8⟩
theorem entry_269_checked : entryAt 269 = entry_269 := by
  rw [entry_chunk_13 3 (by decide)]
  decide +kernel
theorem row_269 : rowAt 269 = data_269 := by
  rw [rowAt, dif_neg (by decide : ¬ 269 < 6), entry_269_checked]
  change forkRow [placeRow ⟨28, 3, 3, 6⟩ (rowAt 28), placeRow ⟨202, 0, 7, 5⟩ (rowAt 202)] = data_269
  rw [row_28, row_202]
  apply row_ext <;> decide +kernel
theorem entry_good_269 : EntryGood 269 := by
  unfold EntryGood
  rw [entry_269_checked]
  decide +kernel
theorem good_269 : Good (rowAt 269) := by
  rw [row_269]
  unfold Good
  decide +kernel

def data_270 : RowData := ⟨{(-1, -1), (0, -1), (0, 1), (0, 2)}, {(-1, -2), (-1, -1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4)}, 6⟩
theorem entry_270_checked : entryAt 270 = entry_270 := by
  rw [entry_chunk_13 4 (by decide)]
  decide +kernel
theorem row_270 : rowAt 270 = data_270 := by
  rw [rowAt, dif_neg (by decide : ¬ 270 < 6), entry_270_checked]
  change forkRow [placeRow ⟨63, 0, 3, 7⟩ (rowAt 63), placeRow ⟨6, 7, 3, 2⟩ (rowAt 6)] = data_270
  rw [row_63, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_270 : EntryGood 270 := by
  unfold EntryGood
  rw [entry_270_checked]
  decide +kernel
theorem good_270 : Good (rowAt 270) := by
  rw [row_270]
  unfold Good
  decide +kernel

def data_271 : RowData := ⟨{(0, -1), (0, 1), (1, -1), (2, -1)}, {(-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 2), (1, 3), (1, 4), (2, -1), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, -2), (5, 0)}, 7⟩
theorem entry_271_checked : entryAt 271 = entry_271 := by
  rw [entry_chunk_13 5 (by decide)]
  decide +kernel
theorem row_271 : rowAt 271 = data_271 := by
  rw [rowAt, dif_neg (by decide : ¬ 271 < 6), entry_271_checked]
  change forkRow [placeRow ⟨107, 2, 7, 3⟩ (rowAt 107), placeRow ⟨107, 3, 4, 6⟩ (rowAt 107)] = data_271
  rw [row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_271 : EntryGood 271 := by
  unfold EntryGood
  rw [entry_271_checked]
  decide +kernel
theorem good_271 : Good (rowAt 271) := by
  rw [row_271]
  unfold Good
  decide +kernel

def data_272 : RowData := ⟨{(-2, -1), (-1, -4), (-1, -2), (-1, -1), (0, -1)}, {(-3, 1), (-2, -1), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -2), (2, 0), (3, -2)}, 9⟩
theorem entry_272_checked : entryAt 272 = entry_272 := by
  rw [entry_chunk_13 6 (by decide)]
  decide +kernel
theorem row_272 : rowAt 272 = data_272 := by
  rw [rowAt, dif_neg (by decide : ¬ 272 < 6), entry_272_checked]
  change forkRow [placeRow ⟨1, 1, 3, 1⟩ (rowAt 1), placeRow ⟨249, 0, 4, 5⟩ (rowAt 249)] = data_272
  rw [row_1, row_249]
  apply row_ext <;> decide +kernel
theorem entry_good_272 : EntryGood 272 := by
  unfold EntryGood
  rw [entry_272_checked]
  decide +kernel
theorem good_272 : Good (rowAt 272) := by
  rw [row_272]
  unfold Good
  decide +kernel

def data_273 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-4, 0), (-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 8⟩
theorem entry_273_checked : entryAt 273 = entry_273 := by
  rw [entry_chunk_13 7 (by decide)]
  decide +kernel
theorem row_273 : rowAt 273 = data_273 := by
  rw [rowAt, dif_neg (by decide : ¬ 273 < 6), entry_273_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨223, 0, 5, 4⟩ (rowAt 223)] = data_273
  rw [row_6, row_223]
  apply row_ext <;> decide +kernel
theorem entry_good_273 : EntryGood 273 := by
  unfold EntryGood
  rw [entry_273_checked]
  decide +kernel
theorem good_273 : Good (rowAt 273) := by
  rw [row_273]
  unfold Good
  decide +kernel

def data_274 : RowData := ⟨{(-1, -2), (0, -2), (0, -1), (0, 1)}, {(-3, 0), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)}, 9⟩
theorem entry_274_checked : entryAt 274 = entry_274 := by
  rw [entry_chunk_13 8 (by decide)]
  decide +kernel
theorem row_274 : rowAt 274 = data_274 := by
  rw [rowAt, dif_neg (by decide : ¬ 274 < 6), entry_274_checked]
  change forkRow [placeRow ⟨6, 7, 3, 1⟩ (rowAt 6), placeRow ⟨240, 0, 5, 5⟩ (rowAt 240)] = data_274
  rw [row_6, row_240]
  apply row_ext <;> decide +kernel
theorem entry_good_274 : EntryGood 274 := by
  unfold EntryGood
  rw [entry_274_checked]
  decide +kernel
theorem good_274 : Good (rowAt 274) := by
  rw [row_274]
  unfold Good
  decide +kernel

def data_275 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-7, -1), (-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 7⟩
theorem entry_275_checked : entryAt 275 = entry_275 := by
  rw [entry_chunk_13 9 (by decide)]
  decide +kernel
theorem row_275 : rowAt 275 = data_275 := by
  rw [rowAt, dif_neg (by decide : ¬ 275 < 6), entry_275_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨198, 4, 0, 4⟩ (rowAt 198), placeRow ⟨44, 2, 5, 4⟩ (rowAt 44)] = data_275
  rw [row_63, row_198, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_275 : EntryGood 275 := by
  unfold EntryGood
  rw [entry_275_checked]
  decide +kernel
theorem good_275 : Good (rowAt 275) := by
  rw [row_275]
  unfold Good
  decide +kernel

def data_276 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1), (3, -2), (3, 0)}, {(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -3), (3, -2), (3, -1), (3, 0), (4, -1)}, 7⟩
theorem entry_276_checked : entryAt 276 = entry_276 := by
  rw [entry_chunk_13 10 (by decide)]
  decide +kernel
theorem row_276 : rowAt 276 = data_276 := by
  rw [rowAt, dif_neg (by decide : ¬ 276 < 6), entry_276_checked]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨177, 0, 5, 4⟩ (rowAt 177), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63)] = data_276
  rw [row_7, row_177, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_276 : EntryGood 276 := by
  unfold EntryGood
  rw [entry_276_checked]
  decide +kernel
theorem good_276 : Good (rowAt 276) := by
  rw [row_276]
  unfold Good
  decide +kernel

def data_277 : RowData := ⟨{(-1, -3), (-1, -1), (0, -1), (1, -3), (1, -2), (1, -1)}, {(-2, -4), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -2)}, 9⟩
theorem entry_277_checked : entryAt 277 = entry_277 := by
  rw [entry_chunk_13 11 (by decide)]
  decide +kernel
theorem row_277 : rowAt 277 = data_277 := by
  rw [rowAt, dif_neg (by decide : ¬ 277 < 6), entry_277_checked]
  change forkRow [placeRow ⟨14, 3, 4, 5⟩ (rowAt 14), placeRow ⟨204, 2, 3, 0⟩ (rowAt 204), placeRow ⟨33, 1, 3, 2⟩ (rowAt 33)] = data_277
  rw [row_14, row_204, row_33]
  apply row_ext <;> decide +kernel
theorem entry_good_277 : EntryGood 277 := by
  unfold EntryGood
  rw [entry_277_checked]
  decide +kernel
theorem good_277 : Good (rowAt 277) := by
  rw [row_277]
  unfold Good
  decide +kernel

def data_278 : RowData := ⟨{(1, 0), (2, -1), (2, 0), (3, 0)}, {(-2, -1), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)}, 7⟩
theorem entry_278_checked : entryAt 278 = entry_278 := by
  rw [entry_chunk_13 12 (by decide)]
  decide +kernel
theorem row_278 : rowAt 278 = data_278 := by
  rw [rowAt, dif_neg (by decide : ¬ 278 < 6), entry_278_checked]
  change forkRow [placeRow ⟨63, 3, 3, 3⟩ (rowAt 63), placeRow ⟨162, 1, 8, 4⟩ (rowAt 162)] = data_278
  rw [row_63, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_278 : EntryGood 278 := by
  unfold EntryGood
  rw [entry_278_checked]
  decide +kernel
theorem good_278 : Good (rowAt 278) := by
  rw [row_278]
  unfold Good
  decide +kernel

def data_279 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, 0)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)}, 8⟩
theorem entry_279_checked : entryAt 279 = entry_279 := by
  rw [entry_chunk_13 13 (by decide)]
  decide +kernel
theorem row_279 : rowAt 279 = data_279 := by
  rw [rowAt, dif_neg (by decide : ¬ 279 < 6), entry_279_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨234, 5, 7, 4⟩ (rowAt 234)] = data_279
  rw [row_6, row_234]
  apply row_ext <;> decide +kernel
theorem entry_good_279 : EntryGood 279 := by
  unfold EntryGood
  rw [entry_279_checked]
  decide +kernel
theorem good_279 : Good (rowAt 279) := by
  rw [row_279]
  unfold Good
  decide +kernel

def data_280 : RowData := ⟨{(-3, -2), (-2, -3), (-2, -2), (-1, -2), (-1, 0), (-1, 1), (0, -2)}, {(-4, -1), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, 0), (-2, 1), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1)}, 5⟩
theorem entry_280_checked : entryAt 280 = entry_280 := by
  rw [entry_chunk_13 14 (by decide)]
  decide +kernel
theorem row_280 : rowAt 280 = data_280 := by
  rw [rowAt, dif_neg (by decide : ¬ 280 < 6), entry_280_checked]
  change forkRow [placeRow ⟨184, 0, 1, 5⟩ (rowAt 184), placeRow ⟨116, 2, 4, 3⟩ (rowAt 116)] = data_280
  rw [row_184, row_116]
  apply row_ext <;> decide +kernel
theorem entry_good_280 : EntryGood 280 := by
  unfold EntryGood
  rw [entry_280_checked]
  decide +kernel
theorem good_280 : Good (rowAt 280) := by
  rw [row_280]
  unfold Good
  decide +kernel

def data_281 : RowData := ⟨{(-2, 0), (-2, 1), (-1, 0), (-1, 1)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 7⟩
theorem entry_281_checked : entryAt 281 = entry_281 := by
  rw [entry_chunk_13 15 (by decide)]
  decide +kernel
theorem row_281 : rowAt 281 = data_281 := by
  rw [rowAt, dif_neg (by decide : ¬ 281 < 6), entry_281_checked]
  change forkRow [placeRow ⟨36, 4, 5, 4⟩ (rowAt 36), placeRow ⟨163, 2, 5, 4⟩ (rowAt 163), placeRow ⟨189, 0, 4, 5⟩ (rowAt 189)] = data_281
  rw [row_36, row_163, row_189]
  apply row_ext <;> decide +kernel
theorem entry_good_281 : EntryGood 281 := by
  unfold EntryGood
  rw [entry_281_checked]
  decide +kernel
theorem good_281 : Good (rowAt 281) := by
  rw [row_281]
  unfold Good
  decide +kernel

def data_282 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 10⟩
theorem entry_282_checked : entryAt 282 = entry_282 := by
  rw [entry_chunk_13 16 (by decide)]
  decide +kernel
theorem row_282 : rowAt 282 = data_282 := by
  rw [rowAt, dif_neg (by decide : ¬ 282 < 6), entry_282_checked]
  change forkRow [placeRow ⟨56, 0, 5, 4⟩ (rowAt 56), placeRow ⟨64, 0, 1, 3⟩ (rowAt 64), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨265, 0, 1, 3⟩ (rowAt 265)] = data_282
  rw [row_56, row_64, row_55, row_265]
  apply row_ext <;> decide +kernel
theorem entry_good_282 : EntryGood 282 := by
  unfold EntryGood
  rw [entry_282_checked]
  decide +kernel
theorem good_282 : Good (rowAt 282) := by
  rw [row_282]
  unfold Good
  decide +kernel

def data_283 : RowData := ⟨{(-3, 0), (-2, 0), (-1, -2), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)}, 9⟩
theorem entry_283_checked : entryAt 283 = entry_283 := by
  rw [entry_chunk_13 17 (by decide)]
  decide +kernel
theorem row_283 : rowAt 283 = data_283 := by
  rw [rowAt, dif_neg (by decide : ¬ 283 < 6), entry_283_checked]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (rowAt 64), placeRow ⟨196, 1, 4, 3⟩ (rowAt 196), placeRow ⟨55, 2, 5, 4⟩ (rowAt 55)] = data_283
  rw [row_64, row_196, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_283 : EntryGood 283 := by
  unfold EntryGood
  rw [entry_283_checked]
  decide +kernel
theorem good_283 : Good (rowAt 283) := by
  rw [row_283]
  unfold Good
  decide +kernel

def data_284 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 9⟩
theorem entry_284_checked : entryAt 284 = entry_284 := by
  rw [entry_chunk_13 18 (by decide)]
  decide +kernel
theorem row_284 : rowAt 284 = data_284 := by
  rw [rowAt, dif_neg (by decide : ¬ 284 < 6), entry_284_checked]
  change forkRow [placeRow ⟨45, 1, 4, 5⟩ (rowAt 45), placeRow ⟨224, 0, 5, 4⟩ (rowAt 224), placeRow ⟨46, 3, 4, 5⟩ (rowAt 46)] = data_284
  rw [row_45, row_224, row_46]
  apply row_ext <;> decide +kernel
theorem entry_good_284 : EntryGood 284 := by
  unfold EntryGood
  rw [entry_284_checked]
  decide +kernel
theorem good_284 : Good (rowAt 284) := by
  rw [row_284]
  unfold Good
  decide +kernel

def data_285 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0)}, {(-2, 0), (-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 9⟩
theorem entry_285_checked : entryAt 285 = entry_285 := by
  rw [entry_chunk_13 19 (by decide)]
  decide +kernel
theorem row_285 : rowAt 285 = data_285 := by
  rw [rowAt, dif_neg (by decide : ¬ 285 < 6), entry_285_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨273, 0, 6, 4⟩ (rowAt 273)] = data_285
  rw [row_6, row_273]
  apply row_ext <;> decide +kernel
theorem entry_good_285 : EntryGood 285 := by
  unfold EntryGood
  rw [entry_285_checked]
  decide +kernel
theorem good_285 : Good (rowAt 285) := by
  rw [row_285]
  unfold Good
  decide +kernel

def data_286 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (0, -1)}, {(-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)}, 10⟩
theorem entry_286_checked : entryAt 286 = entry_286 := by
  rw [entry_chunk_14 0 (by decide)]
  decide +kernel
theorem row_286 : rowAt 286 = data_286 := by
  rw [rowAt, dif_neg (by decide : ¬ 286 < 6), entry_286_checked]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (rowAt 6), placeRow ⟨261, 0, 3, 4⟩ (rowAt 261)] = data_286
  rw [row_6, row_261]
  apply row_ext <;> decide +kernel
theorem entry_good_286 : EntryGood 286 := by
  unfold EntryGood
  rw [entry_286_checked]
  decide +kernel
theorem good_286 : Good (rowAt 286) := by
  rw [row_286]
  unfold Good
  decide +kernel

def data_287 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0), (-1, 1)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 10⟩
theorem entry_287_checked : entryAt 287 = entry_287 := by
  rw [entry_chunk_14 1 (by decide)]
  decide +kernel
theorem row_287 : rowAt 287 = data_287 := by
  rw [rowAt, dif_neg (by decide : ¬ 287 < 6), entry_287_checked]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (rowAt 64), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨56, 0, 5, 4⟩ (rowAt 56), placeRow ⟨264, 4, 4, 5⟩ (rowAt 264)] = data_287
  rw [row_64, row_55, row_56, row_264]
  apply row_ext <;> decide +kernel
theorem entry_good_287 : EntryGood 287 := by
  unfold EntryGood
  rw [entry_287_checked]
  decide +kernel
theorem good_287 : Good (rowAt 287) := by
  rw [row_287]
  unfold Good
  decide +kernel

#check row_287
def data_288 : RowData := ⟨{(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)}, {(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 1), (1, 2)}, 7⟩
theorem entry_288_checked : entryAt 288 = entry_288 := by
  rw [entry_chunk_14 2 (by decide)]
  decide +kernel
theorem row_288 : rowAt 288 = data_288 := by
  rw [rowAt, dif_neg (by decide : ¬ 288 < 6), entry_288_checked]
  change forkRow [placeRow ⟨130, 1, 4, 2⟩ (rowAt 130), placeRow ⟨96, 0, 1, 4⟩ (rowAt 96)] = data_288
  rw [row_130, row_96]
  apply row_ext <;> decide +kernel
theorem entry_good_288 : EntryGood 288 := by
  unfold EntryGood
  rw [entry_288_checked]
  decide +kernel
theorem good_288 : Good (rowAt 288) := by
  rw [row_288]
  unfold Good
  decide +kernel

def data_289 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2)}, {(-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 9⟩
theorem entry_289_checked : entryAt 289 = entry_289 := by
  rw [entry_chunk_14 3 (by decide)]
  decide +kernel
theorem row_289 : rowAt 289 = data_289 := by
  rw [rowAt, dif_neg (by decide : ¬ 289 < 6), entry_289_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨279, 0, 2, 4⟩ (rowAt 279)] = data_289
  rw [row_6, row_279]
  apply row_ext <;> decide +kernel
theorem entry_good_289 : EntryGood 289 := by
  unfold EntryGood
  rw [entry_289_checked]
  decide +kernel
theorem good_289 : Good (rowAt 289) := by
  rw [row_289]
  unfold Good
  decide +kernel

def data_290 : RowData := ⟨{(-2, -1), (-1, -2), (-1, -1), (0, -2), (0, -1), (0, 1)}, {(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -2), (3, -2)}, 8⟩
theorem entry_290_checked : entryAt 290 = entry_290 := by
  rw [entry_chunk_14 4 (by decide)]
  decide +kernel
theorem row_290 : rowAt 290 = data_290 := by
  rw [rowAt, dif_neg (by decide : ¬ 290 < 6), entry_290_checked]
  change forkRow [placeRow ⟨67, 2, 5, 2⟩ (rowAt 67), placeRow ⟨231, 4, 5, 5⟩ (rowAt 231)] = data_290
  rw [row_67, row_231]
  apply row_ext <;> decide +kernel
theorem entry_good_290 : EntryGood 290 := by
  unfold EntryGood
  rw [entry_290_checked]
  decide +kernel
theorem good_290 : Good (rowAt 290) := by
  rw [row_290]
  unfold Good
  decide +kernel

def data_291 : RowData := ⟨{(1, -1), (1, 0), (2, 0), (3, 0)}, {(-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1), (7, 1)}, 8⟩
theorem entry_291_checked : entryAt 291 = entry_291 := by
  rw [entry_chunk_14 5 (by decide)]
  decide +kernel
theorem row_291 : rowAt 291 = data_291 := by
  rw [rowAt, dif_neg (by decide : ¬ 291 < 6), entry_291_checked]
  change forkRow [placeRow ⟨89, 3, 3, 4⟩ (rowAt 89), placeRow ⟨202, 0, 8, 4⟩ (rowAt 202), placeRow ⟨55, 4, 3, 4⟩ (rowAt 55)] = data_291
  rw [row_89, row_202, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_291 : EntryGood 291 := by
  unfold EntryGood
  rw [entry_291_checked]
  decide +kernel
theorem good_291 : Good (rowAt 291) := by
  rw [row_291]
  unfold Good
  decide +kernel

def data_292 : RowData := ⟨{(-3, -1), (-2, -1), (-2, 1), (-1, -1), (-1, 1), (0, 1)}, {(-4, -1), (-3, -1), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0), (2, 0)}, 9⟩
theorem entry_292_checked : entryAt 292 = entry_292 := by
  rw [entry_chunk_14 6 (by decide)]
  decide +kernel
theorem row_292 : rowAt 292 = data_292 := by
  rw [rowAt, dif_neg (by decide : ¬ 292 < 6), entry_292_checked]
  change forkRow [placeRow ⟨39, 0, 3, 4⟩ (rowAt 39), placeRow ⟨219, 3, 3, 4⟩ (rowAt 219), placeRow ⟨79, 1, 4, 3⟩ (rowAt 79)] = data_292
  rw [row_39, row_219, row_79]
  apply row_ext <;> decide +kernel
theorem entry_good_292 : EntryGood 292 := by
  unfold EntryGood
  rw [entry_292_checked]
  decide +kernel
theorem good_292 : Good (rowAt 292) := by
  rw [row_292]
  unfold Good
  decide +kernel

def data_293 : RowData := ⟨{(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2)}, {(-3, -1), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1)}, 6⟩
theorem entry_293_checked : entryAt 293 = entry_293 := by
  rw [entry_chunk_14 7 (by decide)]
  decide +kernel
theorem row_293 : rowAt 293 = data_293 := by
  rw [rowAt, dif_neg (by decide : ¬ 293 < 6), entry_293_checked]
  change forkRow [placeRow ⟨2, 7, 4, 3⟩ (rowAt 2), placeRow ⟨280, 0, 5, 4⟩ (rowAt 280)] = data_293
  rw [row_2, row_280]
  apply row_ext <;> decide +kernel
theorem entry_good_293 : EntryGood 293 := by
  unfold EntryGood
  rw [entry_293_checked]
  decide +kernel
theorem good_293 : Good (rowAt 293) := by
  rw [row_293]
  unfold Good
  decide +kernel

def data_294 : RowData := ⟨{(-3, 0), (-2, -2), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 9⟩
theorem entry_294_checked : entryAt 294 = entry_294 := by
  rw [entry_chunk_14 8 (by decide)]
  decide +kernel
theorem row_294 : rowAt 294 = data_294 := by
  rw [rowAt, dif_neg (by decide : ¬ 294 < 6), entry_294_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨196, 3, 1, 3⟩ (rowAt 196)] = data_294
  rw [row_63, row_196]
  apply row_ext <;> decide +kernel
theorem entry_good_294 : EntryGood 294 := by
  unfold EntryGood
  rw [entry_294_checked]
  decide +kernel
theorem good_294 : Good (rowAt 294) := by
  rw [row_294]
  unfold Good
  decide +kernel

def data_295 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)}, 10⟩
theorem entry_295_checked : entryAt 295 = entry_295 := by
  rw [entry_chunk_14 9 (by decide)]
  decide +kernel
theorem row_295 : rowAt 295 = data_295 := by
  rw [rowAt, dif_neg (by decide : ¬ 295 < 6), entry_295_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨265, 4, 4, 3⟩ (rowAt 265)] = data_295
  rw [row_63, row_64, row_55, row_265]
  apply row_ext <;> decide +kernel
theorem entry_good_295 : EntryGood 295 := by
  unfold EntryGood
  rw [entry_295_checked]
  decide +kernel
theorem good_295 : Good (rowAt 295) := by
  rw [row_295]
  unfold Good
  decide +kernel

def data_296 : RowData := ⟨{(-3, -3), (-3, -2), (-3, -1), (-3, 0), (-1, -2), (0, -2), (0, -1)}, {(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3)}, 7⟩
theorem entry_296_checked : entryAt 296 = entry_296 := by
  rw [entry_chunk_14 10 (by decide)]
  decide +kernel
theorem row_296 : rowAt 296 = data_296 := by
  rw [rowAt, dif_neg (by decide : ¬ 296 < 6), entry_296_checked]
  change forkRow [placeRow ⟨107, 1, 4, 5⟩ (rowAt 107), placeRow ⟨209, 3, 3, 4⟩ (rowAt 209), placeRow ⟨65, 1, 4, 5⟩ (rowAt 65)] = data_296
  rw [row_107, row_209, row_65]
  apply row_ext <;> decide +kernel
theorem entry_good_296 : EntryGood 296 := by
  unfold EntryGood
  rw [entry_296_checked]
  decide +kernel
theorem good_296 : Good (rowAt 296) := by
  rw [row_296]
  unfold Good
  decide +kernel

def data_297 : RowData := ⟨{(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)}, {(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)}, 10⟩
theorem entry_297_checked : entryAt 297 = entry_297 := by
  rw [entry_chunk_14 11 (by decide)]
  decide +kernel
theorem row_297 : rowAt 297 = data_297 := by
  rw [rowAt, dif_neg (by decide : ¬ 297 < 6), entry_297_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨289, 1, 7, 4⟩ (rowAt 289)] = data_297
  rw [row_6, row_289]
  apply row_ext <;> decide +kernel
theorem entry_good_297 : EntryGood 297 := by
  unfold EntryGood
  rw [entry_297_checked]
  decide +kernel
theorem good_297 : Good (rowAt 297) := by
  rw [row_297]
  unfold Good
  decide +kernel

def data_298 : RowData := ⟨{(0, -1), (1, 0), (2, -1), (2, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)}, 8⟩
theorem entry_298_checked : entryAt 298 = entry_298 := by
  rw [entry_chunk_14 12 (by decide)]
  decide +kernel
theorem row_298 : rowAt 298 = data_298 := by
  rw [rowAt, dif_neg (by decide : ¬ 298 < 6), entry_298_checked]
  change forkRow [placeRow ⟨24, 2, 7, 3⟩ (rowAt 24), placeRow ⟨24, 6, 3, 3⟩ (rowAt 24), placeRow ⟨107, 4, 3, 4⟩ (rowAt 107), placeRow ⟨195, 0, 7, 4⟩ (rowAt 195)] = data_298
  rw [row_24, row_107, row_195]
  apply row_ext <;> decide +kernel
theorem entry_good_298 : EntryGood 298 := by
  unfold EntryGood
  rw [entry_298_checked]
  decide +kernel
theorem good_298 : Good (rowAt 298) := by
  rw [row_298]
  unfold Good
  decide +kernel

def data_299 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)}, 10⟩
theorem entry_299_checked : entryAt 299 = entry_299 := by
  rw [entry_chunk_14 13 (by decide)]
  decide +kernel
theorem row_299 : rowAt 299 = data_299 := by
  rw [rowAt, dif_neg (by decide : ¬ 299 < 6), entry_299_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨284, 0, 4, 5⟩ (rowAt 284)] = data_299
  rw [row_6, row_284]
  apply row_ext <;> decide +kernel
theorem entry_good_299 : EntryGood 299 := by
  unfold EntryGood
  rw [entry_299_checked]
  decide +kernel
theorem good_299 : Good (rowAt 299) := by
  rw [row_299]
  unfold Good
  decide +kernel

def data_300 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-3, -2), (-2, -3), (-2, -2), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -2)}, 9⟩
theorem entry_300_checked : entryAt 300 = entry_300 := by
  rw [entry_chunk_14 14 (by decide)]
  decide +kernel
theorem row_300 : rowAt 300 = data_300 := by
  rw [rowAt, dif_neg (by decide : ¬ 300 < 6), entry_300_checked]
  change forkRow [placeRow ⟨64, 3, 5, 1⟩ (rowAt 64), placeRow ⟨240, 2, 5, 1⟩ (rowAt 240), placeRow ⟨55, 3, 4, 5⟩ (rowAt 55)] = data_300
  rw [row_64, row_240, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_300 : EntryGood 300 := by
  unfold EntryGood
  rw [entry_300_checked]
  decide +kernel
theorem good_300 : Good (rowAt 300) := by
  rw [row_300]
  unfold Good
  decide +kernel

def data_301 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 2), (0, -1)}, {(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1)}, 10⟩
theorem entry_301_checked : entryAt 301 = entry_301 := by
  rw [entry_chunk_14 15 (by decide)]
  decide +kernel
theorem row_301 : rowAt 301 = data_301 := by
  rw [rowAt, dif_neg (by decide : ¬ 301 < 6), entry_301_checked]
  change forkRow [placeRow ⟨59, 0, 5, 4⟩ (rowAt 59), placeRow ⟨57, 0, 5, 4⟩ (rowAt 57), placeRow ⟨258, 4, 4, 5⟩ (rowAt 258)] = data_301
  rw [row_59, row_57, row_258]
  apply row_ext <;> decide +kernel
theorem entry_good_301 : EntryGood 301 := by
  unfold EntryGood
  rw [entry_301_checked]
  decide +kernel
theorem good_301 : Good (rowAt 301) := by
  rw [row_301]
  unfold Good
  decide +kernel

def data_302 : RowData := ⟨{(-2, -2), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -2), (2, -1)}, {(-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (4, -1)}, 7⟩
theorem entry_302_checked : entryAt 302 = entry_302 := by
  rw [entry_chunk_14 16 (by decide)]
  decide +kernel
theorem row_302 : rowAt 302 = data_302 := by
  rw [rowAt, dif_neg (by decide : ¬ 302 < 6), entry_302_checked]
  change forkRow [placeRow ⟨125, 0, 5, 3⟩ (rowAt 125), placeRow ⟨162, 4, 3, 6⟩ (rowAt 162)] = data_302
  rw [row_125, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_302 : EntryGood 302 := by
  unfold EntryGood
  rw [entry_302_checked]
  decide +kernel
theorem good_302 : Good (rowAt 302) := by
  rw [row_302]
  unfold Good
  decide +kernel

def data_303 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3)}, {(-2, 0), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)}, 10⟩
theorem entry_303_checked : entryAt 303 = entry_303 := by
  rw [entry_chunk_14 17 (by decide)]
  decide +kernel
theorem row_303 : rowAt 303 = data_303 := by
  rw [rowAt, dif_neg (by decide : ¬ 303 < 6), entry_303_checked]
  change forkRow [placeRow ⟨49, 4, 4, 5⟩ (rowAt 49), placeRow ⟨44, 1, 4, 5⟩ (rowAt 44), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨261, 0, 3, 4⟩ (rowAt 261)] = data_303
  rw [row_49, row_44, row_63, row_261]
  apply row_ext <;> decide +kernel
theorem entry_good_303 : EntryGood 303 := by
  unfold EntryGood
  rw [entry_303_checked]
  decide +kernel
theorem good_303 : Good (rowAt 303) := by
  rw [row_303]
  unfold Good
  decide +kernel

def data_304 : RowData := ⟨{(1, -1), (1, 0), (2, 0), (3, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1), (7, 1)}, 8⟩
theorem entry_304_checked : entryAt 304 = entry_304 := by
  rw [entry_chunk_14 18 (by decide)]
  decide +kernel
theorem row_304 : rowAt 304 = data_304 := by
  rw [rowAt, dif_neg (by decide : ¬ 304 < 6), entry_304_checked]
  change forkRow [placeRow ⟨55, 4, 3, 4⟩ (rowAt 55), placeRow ⟨202, 0, 8, 4⟩ (rowAt 202), placeRow ⟨131, 3, 3, 4⟩ (rowAt 131)] = data_304
  rw [row_55, row_202, row_131]
  apply row_ext <;> decide +kernel
theorem entry_good_304 : EntryGood 304 := by
  unfold EntryGood
  rw [entry_304_checked]
  decide +kernel
theorem good_304 : Good (rowAt 304) := by
  rw [row_304]
  unfold Good
  decide +kernel

def data_305 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 8⟩
theorem entry_305_checked : entryAt 305 = entry_305 := by
  rw [entry_chunk_14 19 (by decide)]
  decide +kernel
theorem row_305 : rowAt 305 = data_305 := by
  rw [rowAt, dif_neg (by decide : ¬ 305 < 6), entry_305_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨278, 0, 1, 4⟩ (rowAt 278)] = data_305
  rw [row_6, row_278]
  apply row_ext <;> decide +kernel
theorem entry_good_305 : EntryGood 305 := by
  unfold EntryGood
  rw [entry_305_checked]
  decide +kernel
theorem good_305 : Good (rowAt 305) := by
  rw [row_305]
  unfold Good
  decide +kernel

def data_306 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)}, {(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, 0), (3, 1), (3, 2)}, 8⟩
theorem entry_306_checked : entryAt 306 = entry_306 := by
  rw [entry_chunk_15 0 (by decide)]
  decide +kernel
theorem row_306 : rowAt 306 = data_306 := by
  rw [rowAt, dif_neg (by decide : ¬ 306 < 6), entry_306_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨288, 0, 6, 4⟩ (rowAt 288)] = data_306
  rw [row_4, row_288]
  apply row_ext <;> decide +kernel
theorem entry_good_306 : EntryGood 306 := by
  unfold EntryGood
  rw [entry_306_checked]
  decide +kernel
theorem good_306 : Good (rowAt 306) := by
  rw [row_306]
  unfold Good
  decide +kernel

def data_307 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 1)}, {(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)}, 9⟩
theorem entry_307_checked : entryAt 307 = entry_307 := by
  rw [entry_chunk_15 1 (by decide)]
  decide +kernel
theorem row_307 : rowAt 307 = data_307 := by
  rw [rowAt, dif_neg (by decide : ¬ 307 < 6), entry_307_checked]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (rowAt 0), placeRow ⟨273, 0, 5, 5⟩ (rowAt 273)] = data_307
  rw [row_0, row_273]
  apply row_ext <;> decide +kernel
theorem entry_good_307 : EntryGood 307 := by
  unfold EntryGood
  rw [entry_307_checked]
  decide +kernel
theorem good_307 : Good (rowAt 307) := by
  rw [row_307]
  unfold Good
  decide +kernel

def data_308 : RowData := ⟨{(0, 1), (1, 1), (2, 1), (3, 1)}, {(-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 4)}, 11⟩
theorem entry_308_checked : entryAt 308 = entry_308 := by
  rw [entry_chunk_15 2 (by decide)]
  decide +kernel
theorem row_308 : rowAt 308 = data_308 := by
  rw [rowAt, dif_neg (by decide : ¬ 308 < 6), entry_308_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨299, 0, 4, 6⟩ (rowAt 299)] = data_308
  rw [row_6, row_299]
  apply row_ext <;> decide +kernel
theorem entry_good_308 : EntryGood 308 := by
  unfold EntryGood
  rw [entry_308_checked]
  decide +kernel
theorem good_308 : Good (rowAt 308) := by
  rw [row_308]
  unfold Good
  decide +kernel

def data_309 : RowData := ⟨{(-2, 0), (0, 1), (0, 2), (0, 3), (1, 1)}, {(-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4)}, 10⟩
theorem entry_309_checked : entryAt 309 = entry_309 := by
  rw [entry_chunk_15 3 (by decide)]
  decide +kernel
theorem row_309 : rowAt 309 = data_309 := by
  rw [rowAt, dif_neg (by decide : ¬ 309 < 6), entry_309_checked]
  change forkRow [placeRow ⟨28, 6, 3, 4⟩ (rowAt 28), placeRow ⟨268, 1, 5, 7⟩ (rowAt 268)] = data_309
  rw [row_28, row_268]
  apply row_ext <;> decide +kernel
theorem entry_good_309 : EntryGood 309 := by
  unfold EntryGood
  rw [entry_309_checked]
  decide +kernel
theorem good_309 : Good (rowAt 309) := by
  rw [row_309]
  unfold Good
  decide +kernel

def data_310 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1)}, {(-3, 0), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (4, -2), (4, 0)}, 8⟩
theorem entry_310_checked : entryAt 310 = entry_310 := by
  rw [entry_chunk_15 4 (by decide)]
  decide +kernel
theorem row_310 : rowAt 310 = data_310 := by
  rw [rowAt, dif_neg (by decide : ¬ 310 < 6), entry_310_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨281, 0, 5, 3⟩ (rowAt 281)] = data_310
  rw [row_6, row_281]
  apply row_ext <;> decide +kernel
theorem entry_good_310 : EntryGood 310 := by
  unfold EntryGood
  rw [entry_310_checked]
  decide +kernel
theorem good_310 : Good (rowAt 310) := by
  rw [row_310]
  unfold Good
  decide +kernel

def data_311 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1), (1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 8⟩
theorem entry_311_checked : entryAt 311 = entry_311 := by
  rw [entry_chunk_15 5 (by decide)]
  decide +kernel
theorem row_311 : rowAt 311 = data_311 := by
  rw [rowAt, dif_neg (by decide : ¬ 311 < 6), entry_311_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨278, 0, 2, 4⟩ (rowAt 278)] = data_311
  rw [row_6, row_278]
  apply row_ext <;> decide +kernel
theorem entry_good_311 : EntryGood 311 := by
  unfold EntryGood
  rw [entry_311_checked]
  decide +kernel
theorem good_311 : Good (rowAt 311) := by
  rw [row_311]
  unfold Good
  decide +kernel

def data_312 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -3), (-1, -1), (-1, 0)}, {(-3, -1), (-3, 2), (-2, -1), (-2, 0), (-2, 2), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1)}, 10⟩
theorem entry_312_checked : entryAt 312 = entry_312 := by
  rw [entry_chunk_15 6 (by decide)]
  decide +kernel
theorem row_312 : rowAt 312 = data_312 := by
  rw [rowAt, dif_neg (by decide : ¬ 312 < 6), entry_312_checked]
  change forkRow [placeRow ⟨9, 2, 5, 4⟩ (rowAt 9), placeRow ⟨272, 0, 4, 5⟩ (rowAt 272)] = data_312
  rw [row_9, row_272]
  apply row_ext <;> decide +kernel
theorem entry_good_312 : EntryGood 312 := by
  unfold EntryGood
  rw [entry_312_checked]
  decide +kernel
theorem good_312 : Good (rowAt 312) := by
  rw [row_312]
  unfold Good
  decide +kernel

def data_313 : RowData := ⟨{(-2, -1), (-1, -1), (0, -3), (0, -2), (0, -1), (1, -1)}, {(-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (3, -2), (3, -1), (4, -2), (4, -1), (5, -2)}, 7⟩
theorem entry_313_checked : entryAt 313 = entry_313 := by
  rw [entry_chunk_15 7 (by decide)]
  decide +kernel
theorem row_313 : rowAt 313 = data_313 := by
  rw [rowAt, dif_neg (by decide : ¬ 313 < 6), entry_313_checked]
  change forkRow [placeRow ⟨162, 4, 4, 5⟩ (rowAt 162), placeRow ⟨148, 5, 6, 3⟩ (rowAt 148)] = data_313
  rw [row_162, row_148]
  apply row_ext <;> decide +kernel
theorem entry_good_313 : EntryGood 313 := by
  unfold EntryGood
  rw [entry_313_checked]
  decide +kernel
theorem good_313 : Good (rowAt 313) := by
  rw [row_313]
  unfold Good
  decide +kernel

def data_314 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 9⟩
theorem entry_314_checked : entryAt 314 = entry_314 := by
  rw [entry_chunk_15 8 (by decide)]
  decide +kernel
theorem row_314 : rowAt 314 = data_314 := by
  rw [rowAt, dif_neg (by decide : ¬ 314 < 6), entry_314_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨305, 0, 6, 4⟩ (rowAt 305)] = data_314
  rw [row_6, row_305]
  apply row_ext <;> decide +kernel
theorem entry_good_314 : EntryGood 314 := by
  unfold EntryGood
  rw [entry_314_checked]
  decide +kernel
theorem good_314 : Good (rowAt 314) := by
  rw [row_314]
  unfold Good
  decide +kernel

def data_315 : RowData := ⟨{(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)}, {(-4, 1), (-4, 2), (-4, 3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (1, 4)}, 8⟩
theorem entry_315_checked : entryAt 315 = entry_315 := by
  rw [entry_chunk_15 9 (by decide)]
  decide +kernel
theorem row_315 : rowAt 315 = data_315 := by
  rw [rowAt, dif_neg (by decide : ¬ 315 < 6), entry_315_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨296, 0, 4, 5⟩ (rowAt 296)] = data_315
  rw [row_6, row_296]
  apply row_ext <;> decide +kernel
theorem entry_good_315 : EntryGood 315 := by
  unfold EntryGood
  rw [entry_315_checked]
  decide +kernel
theorem good_315 : Good (rowAt 315) := by
  rw [row_315]
  unfold Good
  decide +kernel

def data_316 : RowData := ⟨{(0, 1), (0, 2), (0, 3), (1, 1), (2, 1), (3, 1)}, {(-1, 0), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 4), (4, 5), (4, 6)}, 9⟩
theorem entry_316_checked : entryAt 316 = entry_316 := by
  rw [entry_chunk_15 10 (by decide)]
  decide +kernel
theorem row_316 : rowAt 316 = data_316 := by
  rw [rowAt, dif_neg (by decide : ¬ 316 < 6), entry_316_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨306, 0, 5, 8⟩ (rowAt 306)] = data_316
  rw [row_6, row_306]
  apply row_ext <;> decide +kernel
theorem entry_good_316 : EntryGood 316 := by
  unfold EntryGood
  rw [entry_316_checked]
  decide +kernel
theorem good_316 : Good (rowAt 316) := by
  rw [row_316]
  unfold Good
  decide +kernel

def data_317 : RowData := ⟨{(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2), (1, 0)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)}, 9⟩
theorem entry_317_checked : entryAt 317 = entry_317 := by
  rw [entry_chunk_15 11 (by decide)]
  decide +kernel
theorem row_317 : rowAt 317 = data_317 := by
  rw [rowAt, dif_neg (by decide : ¬ 317 < 6), entry_317_checked]
  change forkRow [placeRow ⟨263, 2, 6, 4⟩ (rowAt 263), placeRow ⟨26, 3, 4, 3⟩ (rowAt 26), placeRow ⟨99, 0, 5, 5⟩ (rowAt 99)] = data_317
  rw [row_263, row_26, row_99]
  apply row_ext <;> decide +kernel
theorem entry_good_317 : EntryGood 317 := by
  unfold EntryGood
  rw [entry_317_checked]
  decide +kernel
theorem good_317 : Good (rowAt 317) := by
  rw [row_317]
  unfold Good
  decide +kernel

def data_318 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-2, 0), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)}, 10⟩
theorem entry_318_checked : entryAt 318 = entry_318 := by
  rw [entry_chunk_15 12 (by decide)]
  decide +kernel
theorem row_318 : rowAt 318 = data_318 := by
  rw [rowAt, dif_neg (by decide : ¬ 318 < 6), entry_318_checked]
  change forkRow [placeRow ⟨64, 3, 5, 1⟩ (rowAt 64), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨261, 0, 3, 4⟩ (rowAt 261), placeRow ⟨55, 1, 4, 5⟩ (rowAt 55)] = data_318
  rw [row_64, row_63, row_261, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_318 : EntryGood 318 := by
  unfold EntryGood
  rw [entry_318_checked]
  decide +kernel
theorem good_318 : Good (rowAt 318) := by
  rw [row_318]
  unfold Good
  decide +kernel

def data_319 : RowData := ⟨{(-3, 1), (-2, 1), (-1, 1)}, {(-6, 2), (-5, 1), (-5, 2), (-4, 1), (-4, 2), (-3, 1), (-2, 1), (-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 3), (3, 3)}, 10⟩
theorem entry_319_checked : entryAt 319 = entry_319 := by
  rw [entry_chunk_15 13 (by decide)]
  decide +kernel
theorem row_319 : rowAt 319 = data_319 := by
  rw [rowAt, dif_neg (by decide : ¬ 319 < 6), entry_319_checked]
  change forkRow [placeRow ⟨39, 2, 3, 4⟩ (rowAt 39), placeRow ⟨109, 4, 0, 5⟩ (rowAt 109), placeRow ⟨266, 1, 4, 5⟩ (rowAt 266), placeRow ⟨122, 4, 4, 5⟩ (rowAt 122)] = data_319
  rw [row_39, row_109, row_266, row_122]
  apply row_ext <;> decide +kernel
theorem entry_good_319 : EntryGood 319 := by
  unfold EntryGood
  rw [entry_319_checked]
  decide +kernel
theorem good_319 : Good (rowAt 319) := by
  rw [row_319]
  unfold Good
  decide +kernel

#check row_319
def data_320 : RowData := ⟨{(0, -3), (0, -2), (1, -3), (1, 0), (3, 0)}, {(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1), (6, 1)}, 9⟩
theorem entry_320_checked : entryAt 320 = entry_320 := by
  rw [entry_chunk_15 14 (by decide)]
  decide +kernel
theorem row_320 : rowAt 320 = data_320 := by
  rw [rowAt, dif_neg (by decide : ¬ 320 < 6), entry_320_checked]
  change forkRow [placeRow ⟨19, 1, 4, 3⟩ (rowAt 19), placeRow ⟨267, 2, 6, 4⟩ (rowAt 267), placeRow ⟨115, 7, 4, 3⟩ (rowAt 115)] = data_320
  rw [row_19, row_267, row_115]
  apply row_ext <;> decide +kernel
theorem entry_good_320 : EntryGood 320 := by
  unfold EntryGood
  rw [entry_320_checked]
  decide +kernel
theorem good_320 : Good (rowAt 320) := by
  rw [row_320]
  unfold Good
  decide +kernel

def data_321 : RowData := ⟨{(0, 1), (0, 2), (1, 1), (2, 1)}, {(-3, 3), (-2, 3), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (3, 1), (3, 2), (4, 1), (4, 2), (5, 2)}, 8⟩
theorem entry_321_checked : entryAt 321 = entry_321 := by
  rw [entry_chunk_15 15 (by decide)]
  decide +kernel
theorem row_321 : rowAt 321 = data_321 := by
  rw [rowAt, dif_neg (by decide : ¬ 321 < 6), entry_321_checked]
  change forkRow [placeRow ⟨165, 1, 3, 4⟩ (rowAt 165), placeRow ⟨97, 0, 7, 5⟩ (rowAt 97), placeRow ⟨223, 3, 4, 7⟩ (rowAt 223)] = data_321
  rw [row_165, row_97, row_223]
  apply row_ext <;> decide +kernel
theorem entry_good_321 : EntryGood 321 := by
  unfold EntryGood
  rw [entry_321_checked]
  decide +kernel
theorem good_321 : Good (rowAt 321) := by
  rw [row_321]
  unfold Good
  decide +kernel

def data_322 : RowData := ⟨{(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)}, {(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -4), (2, -2), (2, -1), (2, 0), (2, 1)}, 9⟩
theorem entry_322_checked : entryAt 322 = entry_322 := by
  rw [entry_chunk_15 16 (by decide)]
  decide +kernel
theorem row_322 : rowAt 322 = data_322 := by
  rw [rowAt, dif_neg (by decide : ¬ 322 < 6), entry_322_checked]
  change forkRow [placeRow ⟨96, 0, 1, 4⟩ (rowAt 96), placeRow ⟨205, 1, 5, 2⟩ (rowAt 205)] = data_322
  rw [row_96, row_205]
  apply row_ext <;> decide +kernel
theorem entry_good_322 : EntryGood 322 := by
  unfold EntryGood
  rw [entry_322_checked]
  decide +kernel
theorem good_322 : Good (rowAt 322) := by
  rw [row_322]
  unfold Good
  decide +kernel

def data_323 : RowData := ⟨{(-2, 0), (-1, -2), (-1, -1), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 8⟩
theorem entry_323_checked : entryAt 323 = entry_323 := by
  rw [entry_chunk_15 17 (by decide)]
  decide +kernel
theorem row_323 : rowAt 323 = data_323 := by
  rw [rowAt, dif_neg (by decide : ¬ 323 < 6), entry_323_checked]
  change forkRow [placeRow ⟨165, 6, 4, 5⟩ (rowAt 165), placeRow ⟨278, 0, 1, 4⟩ (rowAt 278), placeRow ⟨25, 1, 4, 5⟩ (rowAt 25)] = data_323
  rw [row_165, row_278, row_25]
  apply row_ext <;> decide +kernel
theorem entry_good_323 : EntryGood 323 := by
  unfold EntryGood
  rw [entry_323_checked]
  decide +kernel
theorem good_323 : Good (rowAt 323) := by
  rw [row_323]
  unfold Good
  decide +kernel

def data_324 : RowData := ⟨{(-1, -1), (1, -3), (1, -2), (1, -1), (1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 9⟩
theorem entry_324_checked : entryAt 324 = entry_324 := by
  rw [entry_chunk_15 18 (by decide)]
  decide +kernel
theorem row_324 : rowAt 324 = data_324 := by
  rw [rowAt, dif_neg (by decide : ¬ 324 < 6), entry_324_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨298, 0, 3, 4⟩ (rowAt 298)] = data_324
  rw [row_6, row_298]
  apply row_ext <;> decide +kernel
theorem entry_good_324 : EntryGood 324 := by
  unfold EntryGood
  rw [entry_324_checked]
  decide +kernel
theorem good_324 : Good (rowAt 324) := by
  rw [row_324]
  unfold Good
  decide +kernel

def data_325 : RowData := ⟨{(-1, 0), (1, -2), (1, -1), (1, 0), (1, 1)}, {(-2, 0), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)}, 8⟩
theorem entry_325_checked : entryAt 325 = entry_325 := by
  rw [entry_chunk_15 19 (by decide)]
  decide +kernel
theorem row_325 : rowAt 325 = data_325 := by
  rw [rowAt, dif_neg (by decide : ¬ 325 < 6), entry_325_checked]
  change forkRow [placeRow ⟨25, 0, 6, 5⟩ (rowAt 25), placeRow ⟨313, 1, 6, 4⟩ (rowAt 313), placeRow ⟨24, 2, 6, 3⟩ (rowAt 24)] = data_325
  rw [row_25, row_313, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_325 : EntryGood 325 := by
  unfold EntryGood
  rw [entry_325_checked]
  decide +kernel
theorem good_325 : Good (rowAt 325) := by
  rw [row_325]
  unfold Good
  decide +kernel

def data_326 : RowData := ⟨{(-4, -3), (-3, 0), (-2, 0), (-1, 0)}, {(-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 1), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 10⟩
theorem entry_326_checked : entryAt 326 = entry_326 := by
  rw [entry_chunk_16 0 (by decide)]
  decide +kernel
theorem row_326 : rowAt 326 = data_326 := by
  rw [rowAt, dif_neg (by decide : ¬ 326 < 6), entry_326_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨255, 7, 0, 4⟩ (rowAt 255)] = data_326
  rw [row_63, row_255]
  apply row_ext <;> decide +kernel
theorem entry_good_326 : EntryGood 326 := by
  unfold EntryGood
  rw [entry_326_checked]
  decide +kernel
theorem good_326 : Good (rowAt 326) := by
  rw [row_326]
  unfold Good
  decide +kernel

def data_327 : RowData := ⟨{(-1, -1), (-1, 0), (1, -1), (1, 0)}, {(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 8⟩
theorem entry_327_checked : entryAt 327 = entry_327 := by
  rw [entry_chunk_16 1 (by decide)]
  decide +kernel
theorem row_327 : rowAt 327 = data_327 := by
  rw [rowAt, dif_neg (by decide : ¬ 327 < 6), entry_327_checked]
  change forkRow [placeRow ⟨24, 2, 6, 3⟩ (rowAt 24), placeRow ⟨195, 4, 2, 4⟩ (rowAt 195), placeRow ⟨195, 0, 6, 4⟩ (rowAt 195), placeRow ⟨24, 6, 2, 3⟩ (rowAt 24)] = data_327
  rw [row_24, row_195]
  apply row_ext <;> decide +kernel
theorem entry_good_327 : EntryGood 327 := by
  unfold EntryGood
  rw [entry_327_checked]
  decide +kernel
theorem good_327 : Good (rowAt 327) := by
  rw [row_327]
  unfold Good
  decide +kernel

def data_328 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (0, -1)}, {(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 10⟩
theorem entry_328_checked : entryAt 328 = entry_328 := by
  rw [entry_chunk_16 2 (by decide)]
  decide +kernel
theorem row_328 : rowAt 328 = data_328 := by
  rw [rowAt, dif_neg (by decide : ¬ 328 < 6), entry_328_checked]
  change forkRow [placeRow ⟨49, 0, 4, 5⟩ (rowAt 49), placeRow ⟨44, 3, 4, 5⟩ (rowAt 44), placeRow ⟨285, 0, 3, 4⟩ (rowAt 285)] = data_328
  rw [row_49, row_44, row_285]
  apply row_ext <;> decide +kernel
theorem entry_good_328 : EntryGood 328 := by
  unfold EntryGood
  rw [entry_328_checked]
  decide +kernel
theorem good_328 : Good (rowAt 328) := by
  rw [row_328]
  unfold Good
  decide +kernel

def data_329 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 1)}, {(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)}, 9⟩
theorem entry_329_checked : entryAt 329 = entry_329 := by
  rw [entry_chunk_16 3 (by decide)]
  decide +kernel
theorem row_329 : rowAt 329 = data_329 := by
  rw [rowAt, dif_neg (by decide : ¬ 329 < 6), entry_329_checked]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (rowAt 0), placeRow ⟨305, 0, 5, 5⟩ (rowAt 305)] = data_329
  rw [row_0, row_305]
  apply row_ext <;> decide +kernel
theorem entry_good_329 : EntryGood 329 := by
  unfold EntryGood
  rw [entry_329_checked]
  decide +kernel
theorem good_329 : Good (rowAt 329) := by
  rw [row_329]
  unfold Good
  decide +kernel

def data_330 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2)}, 10⟩
theorem entry_330_checked : entryAt 330 = entry_330 := by
  rw [entry_chunk_16 4 (by decide)]
  decide +kernel
theorem row_330 : rowAt 330 = data_330 := by
  rw [rowAt, dif_neg (by decide : ¬ 330 < 6), entry_330_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨268, 0, 4, 5⟩ (rowAt 268), placeRow ⟨144, 0, 5, 4⟩ (rowAt 144), placeRow ⟨154, 4, 5, 4⟩ (rowAt 154), placeRow ⟨155, 5, 5, 4⟩ (rowAt 155)] = data_330
  rw [row_63, row_268, row_144, row_154, row_155]
  apply row_ext <;> decide +kernel
theorem entry_good_330 : EntryGood 330 := by
  unfold EntryGood
  rw [entry_330_checked]
  decide +kernel
theorem good_330 : Good (rowAt 330) := by
  rw [row_330]
  unfold Good
  decide +kernel

def data_331 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-2, 1), (-1, 1)}, {(-7, 0), (-6, 0), (-6, 1), (-6, 2), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 2)}, 9⟩
theorem entry_331_checked : entryAt 331 = entry_331 := by
  rw [entry_chunk_16 5 (by decide)]
  decide +kernel
theorem row_331 : rowAt 331 = data_331 := by
  rw [rowAt, dif_neg (by decide : ¬ 331 < 6), entry_331_checked]
  change forkRow [placeRow ⟨113, 0, 1, 4⟩ (rowAt 113), placeRow ⟨15, 0, 3, 4⟩ (rowAt 15), placeRow ⟨298, 4, 4, 5⟩ (rowAt 298), placeRow ⟨90, 2, 5, 4⟩ (rowAt 90)] = data_331
  rw [row_113, row_15, row_298, row_90]
  apply row_ext <;> decide +kernel
theorem entry_good_331 : EntryGood 331 := by
  unfold EntryGood
  rw [entry_331_checked]
  decide +kernel
theorem good_331 : Good (rowAt 331) := by
  rw [row_331]
  unfold Good
  decide +kernel

def data_332 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -1), (1, 0)}, {(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -4), (2, -3), (2, -2), (2, -1), (3, -4), (3, -3), (3, -2), (4, -4), (4, -3), (4, -2), (5, -4), (5, -3), (5, -2), (6, -2)}, 10⟩
theorem entry_332_checked : entryAt 332 = entry_332 := by
  rw [entry_chunk_16 6 (by decide)]
  decide +kernel
theorem row_332 : rowAt 332 = data_332 := by
  rw [rowAt, dif_neg (by decide : ¬ 332 < 6), entry_332_checked]
  change forkRow [placeRow ⟨67, 4, 3, 4⟩ (rowAt 67), placeRow ⟨289, 2, 5, 1⟩ (rowAt 289)] = data_332
  rw [row_67, row_289]
  apply row_ext <;> decide +kernel
theorem entry_good_332 : EntryGood 332 := by
  unfold EntryGood
  rw [entry_332_checked]
  decide +kernel
theorem good_332 : Good (rowAt 332) := by
  rw [row_332]
  unfold Good
  decide +kernel

def data_333 : RowData := ⟨{(0, -3), (0, -2), (1, -4), (1, -3), (1, -2), (2, 0)}, {(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 10⟩
theorem entry_333_checked : entryAt 333 = entry_333 := by
  rw [entry_chunk_16 7 (by decide)]
  decide +kernel
theorem row_333 : rowAt 333 = data_333 := by
  rw [rowAt, dif_neg (by decide : ¬ 333 < 6), entry_333_checked]
  change forkRow [placeRow ⟨317, 0, 5, 4⟩ (rowAt 317), placeRow ⟨1, 5, 4, 3⟩ (rowAt 1)] = data_333
  rw [row_317, row_1]
  apply row_ext <;> decide +kernel
theorem entry_good_333 : EntryGood 333 := by
  unfold EntryGood
  rw [entry_333_checked]
  decide +kernel
theorem good_333 : Good (rowAt 333) := by
  rw [row_333]
  unfold Good
  decide +kernel

def data_334 : RowData := ⟨{(0, -2), (0, -1), (0, 1), (1, -2), (1, -1)}, {(-3, -2), (-2, -2), (-1, -3), (-1, -2), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0)}, 10⟩
theorem entry_334_checked : entryAt 334 = entry_334 := by
  rw [entry_chunk_16 8 (by decide)]
  decide +kernel
theorem row_334 : rowAt 334 = data_334 := by
  rw [rowAt, dif_neg (by decide : ¬ 334 < 6), entry_334_checked]
  change forkRow [placeRow ⟨67, 6, 3, 2⟩ (rowAt 67), placeRow ⟨289, 0, 5, 5⟩ (rowAt 289)] = data_334
  rw [row_67, row_289]
  apply row_ext <;> decide +kernel
theorem entry_good_334 : EntryGood 334 := by
  unfold EntryGood
  rw [entry_334_checked]
  decide +kernel
theorem good_334 : Good (rowAt 334) := by
  rw [row_334]
  unfold Good
  decide +kernel

def data_335 : RowData := ⟨{(-3, 0), (-2, -2), (-2, 0), (-1, -1), (-1, 0)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 9⟩
theorem entry_335_checked : entryAt 335 = entry_335 := by
  rw [entry_chunk_16 9 (by decide)]
  decide +kernel
theorem row_335 : rowAt 335 = data_335 := by
  rw [rowAt, dif_neg (by decide : ¬ 335 < 6), entry_335_checked]
  change forkRow [placeRow ⟨196, 3, 1, 3⟩ (rowAt 196), placeRow ⟨162, 1, 5, 4⟩ (rowAt 162)] = data_335
  rw [row_196, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_335 : EntryGood 335 := by
  unfold EntryGood
  rw [entry_335_checked]
  decide +kernel
theorem good_335 : Good (rowAt 335) := by
  rw [row_335]
  unfold Good
  decide +kernel

def data_336 : RowData := ⟨{(-1, -1), (-1, 0), (1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 9⟩
theorem entry_336_checked : entryAt 336 = entry_336 := by
  rw [entry_chunk_16 10 (by decide)]
  decide +kernel
theorem row_336 : rowAt 336 = data_336 := by
  rw [rowAt, dif_neg (by decide : ¬ 336 < 6), entry_336_checked]
  change forkRow [placeRow ⟨25, 6, 2, 3⟩ (rowAt 25), placeRow ⟨199, 3, 2, 4⟩ (rowAt 199), placeRow ⟨65, 0, 6, 4⟩ (rowAt 65), placeRow ⟨304, 0, 2, 4⟩ (rowAt 304)] = data_336
  rw [row_25, row_199, row_65, row_304]
  apply row_ext <;> decide +kernel
theorem entry_good_336 : EntryGood 336 := by
  unfold EntryGood
  rw [entry_336_checked]
  decide +kernel
theorem good_336 : Good (rowAt 336) := by
  rw [row_336]
  unfold Good
  decide +kernel

def data_337 : RowData := ⟨{(-3, 0), (-1, 0), (-1, 1), (-1, 2)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 9⟩
theorem entry_337_checked : entryAt 337 = entry_337 := by
  rw [entry_chunk_16 11 (by decide)]
  decide +kernel
theorem row_337 : rowAt 337 = data_337 := by
  rw [rowAt, dif_neg (by decide : ¬ 337 < 6), entry_337_checked]
  change forkRow [placeRow ⟨107, 3, 3, 7⟩ (rowAt 107), placeRow ⟨230, 2, 1, 5⟩ (rowAt 230)] = data_337
  rw [row_107, row_230]
  apply row_ext <;> decide +kernel
theorem entry_good_337 : EntryGood 337 := by
  unfold EntryGood
  rw [entry_337_checked]
  decide +kernel
theorem good_337 : Good (rowAt 337) := by
  rw [row_337]
  unfold Good
  decide +kernel

def data_338 : RowData := ⟨{(-1, 0), (1, -2), (1, -1), (1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)}, 8⟩
theorem entry_338_checked : entryAt 338 = entry_338 := by
  rw [entry_chunk_16 12 (by decide)]
  decide +kernel
theorem row_338 : rowAt 338 = data_338 := by
  rw [rowAt, dif_neg (by decide : ¬ 338 < 6), entry_338_checked]
  change forkRow [placeRow ⟨241, 0, 6, 4⟩ (rowAt 241), placeRow ⟨275, 4, 2, 4⟩ (rowAt 275), placeRow ⟨107, 4, 2, 4⟩ (rowAt 107)] = data_338
  rw [row_241, row_275, row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_338 : EntryGood 338 := by
  unfold EntryGood
  rw [entry_338_checked]
  decide +kernel
theorem good_338 : Good (rowAt 338) := by
  rw [row_338]
  unfold Good
  decide +kernel

def data_339 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)}, {(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (1, -3), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (4, -4), (4, -2), (4, -1), (4, 0), (4, 1)}, 10⟩
theorem entry_339_checked : entryAt 339 = entry_339 := by
  rw [entry_chunk_16 13 (by decide)]
  decide +kernel
theorem row_339 : rowAt 339 = data_339 := by
  rw [rowAt, dif_neg (by decide : ¬ 339 < 6), entry_339_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨322, 0, 6, 4⟩ (rowAt 322)] = data_339
  rw [row_4, row_322]
  apply row_ext <;> decide +kernel
theorem entry_good_339 : EntryGood 339 := by
  unfold EntryGood
  rw [entry_339_checked]
  decide +kernel
theorem good_339 : Good (rowAt 339) := by
  rw [row_339]
  unfold Good
  decide +kernel

def data_340 : RowData := ⟨{(-1, 1), (0, -1), (0, 1)}, {(-4, -2), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (3, 0)}, 10⟩
theorem entry_340_checked : entryAt 340 = entry_340 := by
  rw [entry_chunk_16 14 (by decide)]
  decide +kernel
theorem row_340 : rowAt 340 = data_340 := by
  rw [rowAt, dif_neg (by decide : ¬ 340 < 6), entry_340_checked]
  change forkRow [placeRow ⟨25, 3, 3, 6⟩ (rowAt 25), placeRow ⟨300, 4, 4, 6⟩ (rowAt 300), placeRow ⟨24, 3, 3, 6⟩ (rowAt 24)] = data_340
  rw [row_25, row_300, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_340 : EntryGood 340 := by
  unfold EntryGood
  rw [entry_340_checked]
  decide +kernel
theorem good_340 : Good (rowAt 340) := by
  rw [row_340]
  unfold Good
  decide +kernel

def data_341 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0), (-1, 1)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)}, 9⟩
theorem entry_341_checked : entryAt 341 = entry_341 := by
  rw [entry_chunk_16 15 (by decide)]
  decide +kernel
theorem row_341 : rowAt 341 = data_341 := by
  rw [rowAt, dif_neg (by decide : ¬ 341 < 6), entry_341_checked]
  change forkRow [placeRow ⟨162, 5, 5, 4⟩ (rowAt 162), placeRow ⟨259, 4, 4, 5⟩ (rowAt 259), placeRow ⟨208, 2, 5, 4⟩ (rowAt 208), placeRow ⟨143, 0, 1, 3⟩ (rowAt 143)] = data_341
  rw [row_162, row_259, row_208, row_143]
  apply row_ext <;> decide +kernel
theorem entry_good_341 : EntryGood 341 := by
  unfold EntryGood
  rw [entry_341_checked]
  decide +kernel
theorem good_341 : Good (rowAt 341) := by
  rw [row_341]
  unfold Good
  decide +kernel

def data_342 : RowData := ⟨{(-2, -2), (-1, -3), (-1, -2), (0, -3), (0, -2)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (3, -3), (3, -2), (3, -1)}, 9⟩
theorem entry_342_checked : entryAt 342 = entry_342 := by
  rw [entry_chunk_16 16 (by decide)]
  decide +kernel
theorem row_342 : rowAt 342 = data_342 := by
  rw [rowAt, dif_neg (by decide : ¬ 342 < 6), entry_342_checked]
  change forkRow [placeRow ⟨210, 0, 5, 2⟩ (rowAt 210), placeRow ⟨88, 1, 4, 3⟩ (rowAt 88), placeRow ⟨260, 4, 4, 3⟩ (rowAt 260), placeRow ⟨290, 0, 4, 3⟩ (rowAt 290)] = data_342
  rw [row_210, row_88, row_260, row_290]
  apply row_ext <;> decide +kernel
theorem entry_good_342 : EntryGood 342 := by
  unfold EntryGood
  rw [entry_342_checked]
  decide +kernel
theorem good_342 : Good (rowAt 342) := by
  rw [row_342]
  unfold Good
  decide +kernel

def data_343 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3), (1, -2)}, {(-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 9⟩
theorem entry_343_checked : entryAt 343 = entry_343 := by
  rw [entry_chunk_16 17 (by decide)]
  decide +kernel
theorem row_343 : rowAt 343 = data_343 := by
  rw [rowAt, dif_neg (by decide : ¬ 343 < 6), entry_343_checked]
  change forkRow [placeRow ⟨0, 5, 4, 5⟩ (rowAt 0), placeRow ⟨250, 0, 5, 4⟩ (rowAt 250)] = data_343
  rw [row_0, row_250]
  apply row_ext <;> decide +kernel
theorem entry_good_343 : EntryGood 343 := by
  unfold EntryGood
  rw [entry_343_checked]
  decide +kernel
theorem good_343 : Good (rowAt 343) := by
  rw [row_343]
  unfold Good
  decide +kernel

def data_344 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1), (1, -3), (2, -3), (3, -3), (3, -2)}, {(-1, -1), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 10⟩
theorem entry_344_checked : entryAt 344 = entry_344 := by
  rw [entry_chunk_16 18 (by decide)]
  decide +kernel
theorem row_344 : rowAt 344 = data_344 := by
  rw [rowAt, dif_neg (by decide : ¬ 344 < 6), entry_344_checked]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (rowAt 7), placeRow ⟨108, 3, 4, 5⟩ (rowAt 108), placeRow ⟨262, 4, 5, 2⟩ (rowAt 262)] = data_344
  rw [row_7, row_108, row_262]
  apply row_ext <;> decide +kernel
theorem entry_good_344 : EntryGood 344 := by
  unfold EntryGood
  rw [entry_344_checked]
  decide +kernel
theorem good_344 : Good (rowAt 344) := by
  rw [row_344]
  unfold Good
  decide +kernel

def data_345 : RowData := ⟨{(-3, 0), (-3, 3), (-2, 0), (-1, 0), (-1, 3), (0, 1)}, {(-6, 4), (-5, 3), (-5, 4), (-4, 3), (-4, 4), (-3, 0), (-3, 3), (-3, 4), (-2, 0), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4)}, 10⟩
theorem entry_345_checked : entryAt 345 = entry_345 := by
  rw [entry_chunk_16 19 (by decide)]
  decide +kernel
theorem row_345 : rowAt 345 = data_345 := by
  rw [rowAt, dif_neg (by decide : ¬ 345 < 6), entry_345_checked]
  change forkRow [placeRow ⟨6, 0, 5, 5⟩ (rowAt 6), placeRow ⟨320, 4, 4, 7⟩ (rowAt 320)] = data_345
  rw [row_6, row_320]
  apply row_ext <;> decide +kernel
theorem entry_good_345 : EntryGood 345 := by
  unfold EntryGood
  rw [entry_345_checked]
  decide +kernel
theorem good_345 : Good (rowAt 345) := by
  rw [row_345]
  unfold Good
  decide +kernel

def data_346 : RowData := ⟨{(-3, -4), (-3, -3), (-3, -2), (-3, -1), (-1, -3), (0, -3), (0, -2)}, {(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2)}, 10⟩
theorem entry_346_checked : entryAt 346 = entry_346 := by
  rw [entry_chunk_17 0 (by decide)]
  decide +kernel
theorem row_346 : rowAt 346 = data_346 := by
  rw [rowAt, dif_neg (by decide : ¬ 346 < 6), entry_346_checked]
  change forkRow [placeRow ⟨60, 1, 4, 3⟩ (rowAt 60), placeRow ⟨255, 0, 1, 4⟩ (rowAt 255), placeRow ⟨276, 0, 1, 4⟩ (rowAt 276)] = data_346
  rw [row_60, row_255, row_276]
  apply row_ext <;> decide +kernel
theorem entry_good_346 : EntryGood 346 := by
  unfold EntryGood
  rw [entry_346_checked]
  decide +kernel
theorem good_346 : Good (rowAt 346) := by
  rw [row_346]
  unfold Good
  decide +kernel

def data_347 : RowData := ⟨{(0, 1), (0, 2), (0, 3), (1, 1), (2, 1), (3, 1)}, {(-1, 0), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 1), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 2), (5, 3), (5, 4), (5, 5)}, 11⟩
theorem entry_347_checked : entryAt 347 = entry_347 := by
  rw [entry_chunk_17 1 (by decide)]
  decide +kernel
theorem row_347 : rowAt 347 = data_347 := by
  rw [rowAt, dif_neg (by decide : ¬ 347 < 6), entry_347_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨339, 0, 5, 8⟩ (rowAt 339)] = data_347
  rw [row_6, row_339]
  apply row_ext <;> decide +kernel
theorem entry_good_347 : EntryGood 347 := by
  unfold EntryGood
  rw [entry_347_checked]
  decide +kernel
theorem good_347 : Good (rowAt 347) := by
  rw [row_347]
  unfold Good
  decide +kernel

def data_348 : RowData := ⟨{(-2, 0), (-2, 1), (-1, -1), (0, -2), (0, -1), (1, -1), (1, 0)}, {(-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)}, 11⟩
theorem entry_348_checked : entryAt 348 = entry_348 := by
  rw [entry_chunk_17 2 (by decide)]
  decide +kernel
theorem row_348 : rowAt 348 = data_348 := by
  rw [rowAt, dif_neg (by decide : ¬ 348 < 6), entry_348_checked]
  change forkRow [placeRow ⟨312, 1, 5, 5⟩ (rowAt 312), placeRow ⟨114, 4, 3, 4⟩ (rowAt 114), placeRow ⟨139, 3, 4, 5⟩ (rowAt 139)] = data_348
  rw [row_312, row_114, row_139]
  apply row_ext <;> decide +kernel
theorem entry_good_348 : EntryGood 348 := by
  unfold EntryGood
  rw [entry_348_checked]
  decide +kernel
theorem good_348 : Good (rowAt 348) := by
  rw [row_348]
  unfold Good
  decide +kernel

def data_349 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (0, -1)}, {(-4, 0), (-3, 0), (-2, -4), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -3), (4, -2), (5, -2)}, 11⟩
theorem entry_349_checked : entryAt 349 = entry_349 := by
  rw [entry_chunk_17 3 (by decide)]
  decide +kernel
theorem row_349 : rowAt 349 = data_349 := by
  rw [rowAt, dif_neg (by decide : ¬ 349 < 6), entry_349_checked]
  change forkRow [placeRow ⟨14, 1, 4, 5⟩ (rowAt 14), placeRow ⟨17, 1, 4, 5⟩ (rowAt 17), placeRow ⟨332, 0, 3, 4⟩ (rowAt 332)] = data_349
  rw [row_14, row_17, row_332]
  apply row_ext <;> decide +kernel
theorem entry_good_349 : EntryGood 349 := by
  unfold EntryGood
  rw [entry_349_checked]
  decide +kernel
theorem good_349 : Good (rowAt 349) := by
  rw [row_349]
  unfold Good
  decide +kernel

def data_350 : RowData := ⟨{(-1, 0), (-1, 1), (1, 0), (1, 2)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 8⟩
theorem entry_350_checked : entryAt 350 = entry_350 := by
  rw [entry_chunk_17 4 (by decide)]
  decide +kernel
theorem row_350 : rowAt 350 = data_350 := by
  rw [rowAt, dif_neg (by decide : ¬ 350 < 6), entry_350_checked]
  change forkRow [placeRow ⟨24, 4, 2, 5⟩ (rowAt 24), placeRow ⟨107, 2, 6, 4⟩ (rowAt 107), placeRow ⟨271, 4, 5, 5⟩ (rowAt 271), placeRow ⟨215, 0, 5, 5⟩ (rowAt 215)] = data_350
  rw [row_24, row_107, row_271, row_215]
  apply row_ext <;> decide +kernel
theorem entry_good_350 : EntryGood 350 := by
  unfold EntryGood
  rw [entry_350_checked]
  decide +kernel
theorem good_350 : Good (rowAt 350) := by
  rw [row_350]
  unfold Good
  decide +kernel

def data_351 : RowData := ⟨{(-2, -1), (-2, 0), (-2, 1), (-1, 0)}, {(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 11⟩
theorem entry_351_checked : entryAt 351 = entry_351 := by
  rw [entry_chunk_17 5 (by decide)]
  decide +kernel
theorem row_351 : rowAt 351 = data_351 := by
  rw [rowAt, dif_neg (by decide : ¬ 351 < 6), entry_351_checked]
  change forkRow [placeRow ⟨163, 0, 5, 4⟩ (rowAt 163), placeRow ⟨287, 4, 1, 4⟩ (rowAt 287), placeRow ⟨25, 4, 1, 5⟩ (rowAt 25)] = data_351
  rw [row_163, row_287, row_25]
  apply row_ext <;> decide +kernel
theorem entry_good_351 : EntryGood 351 := by
  unfold EntryGood
  rw [entry_351_checked]
  decide +kernel
theorem good_351 : Good (rowAt 351) := by
  rw [row_351]
  unfold Good
  decide +kernel

#check row_351
def data_352 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)}, 11⟩
theorem entry_352_checked : entryAt 352 = entry_352 := by
  rw [entry_chunk_17 6 (by decide)]
  decide +kernel
theorem row_352 : rowAt 352 = data_352 := by
  rw [rowAt, dif_neg (by decide : ¬ 352 < 6), entry_352_checked]
  change forkRow [placeRow ⟨214, 0, 4, 5⟩ (rowAt 214), placeRow ⟨91, 0, 3, 4⟩ (rowAt 91), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨344, 0, 4, 5⟩ (rowAt 344), placeRow ⟨180, 4, 4, 5⟩ (rowAt 180)] = data_352
  rw [row_214, row_91, row_63, row_344, row_180]
  apply row_ext <;> decide +kernel
theorem entry_good_352 : EntryGood 352 := by
  unfold EntryGood
  rw [entry_352_checked]
  decide +kernel
theorem good_352 : Good (rowAt 352) := by
  rw [row_352]
  unfold Good
  decide +kernel

def data_353 : RowData := ⟨{(-3, 0), (-3, 1), (-3, 2), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 1), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4)}, 12⟩
theorem entry_353_checked : entryAt 353 = entry_353 := by
  rw [entry_chunk_17 7 (by decide)]
  decide +kernel
theorem row_353 : rowAt 353 = data_353 := by
  rw [rowAt, dif_neg (by decide : ¬ 353 < 6), entry_353_checked]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (rowAt 6), placeRow ⟨347, 0, 1, 3⟩ (rowAt 347)] = data_353
  rw [row_6, row_347]
  apply row_ext <;> decide +kernel
theorem entry_good_353 : EntryGood 353 := by
  unfold EntryGood
  rw [entry_353_checked]
  decide +kernel
theorem good_353 : Good (rowAt 353) := by
  rw [row_353]
  unfold Good
  decide +kernel

def data_354 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (0, -2), (0, 1), (1, -2)}, {(-3, 0), (-2, -1), (-2, 0), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 0)}, 11⟩
theorem entry_354_checked : entryAt 354 = entry_354 := by
  rw [entry_chunk_17 8 (by decide)]
  decide +kernel
theorem row_354 : rowAt 354 = data_354 := by
  rw [rowAt, dif_neg (by decide : ¬ 354 < 6), entry_354_checked]
  change forkRow [placeRow ⟨138, 2, 5, 4⟩ (rowAt 138), placeRow ⟨114, 5, 4, 3⟩ (rowAt 114), placeRow ⟨312, 0, 5, 5⟩ (rowAt 312), placeRow ⟨182, 2, 2, 4⟩ (rowAt 182)] = data_354
  rw [row_138, row_114, row_312, row_182]
  apply row_ext <;> decide +kernel
theorem entry_good_354 : EntryGood 354 := by
  unfold EntryGood
  rw [entry_354_checked]
  decide +kernel
theorem good_354 : Good (rowAt 354) := by
  rw [row_354]
  unfold Good
  decide +kernel

def data_355 : RowData := ⟨{(1, -1), (1, 0), (2, -1), (2, 0)}, {(-2, 0), (-2, 1), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)}, 10⟩
theorem entry_355_checked : entryAt 355 = entry_355 := by
  rw [entry_chunk_17 9 (by decide)]
  decide +kernel
theorem row_355 : rowAt 355 = data_355 := by
  rw [rowAt, dif_neg (by decide : ¬ 355 < 6), entry_355_checked]
  change forkRow [placeRow ⟨12, 2, 7, 3⟩ (rowAt 12), placeRow ⟨167, 0, 7, 4⟩ (rowAt 167), placeRow ⟨342, 0, 6, 6⟩ (rowAt 342)] = data_355
  rw [row_12, row_167, row_342]
  apply row_ext <;> decide +kernel
theorem entry_good_355 : EntryGood 355 := by
  unfold EntryGood
  rw [entry_355_checked]
  decide +kernel
theorem good_355 : Good (rowAt 355) := by
  rw [row_355]
  unfold Good
  decide +kernel

def data_356 : RowData := ⟨{(-1, -1), (-1, 0), (1, -1), (1, 0), (1, 1)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (5, -1), (5, 0), (6, -1)}, 8⟩
theorem entry_356_checked : entryAt 356 = entry_356 := by
  rw [entry_chunk_17 10 (by decide)]
  decide +kernel
theorem row_356 : rowAt 356 = data_356 := by
  rw [rowAt, dif_neg (by decide : ¬ 356 < 6), entry_356_checked]
  change forkRow [placeRow ⟨24, 2, 6, 3⟩ (rowAt 24), placeRow ⟨24, 6, 2, 3⟩ (rowAt 24), placeRow ⟨211, 4, 2, 4⟩ (rowAt 211), placeRow ⟨179, 0, 6, 4⟩ (rowAt 179)] = data_356
  rw [row_24, row_211, row_179]
  apply row_ext <;> decide +kernel
theorem entry_good_356 : EntryGood 356 := by
  unfold EntryGood
  rw [entry_356_checked]
  decide +kernel
theorem good_356 : Good (rowAt 356) := by
  rw [row_356]
  unfold Good
  decide +kernel

def data_357 : RowData := ⟨{(-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 2)}, {(-4, -1), (-3, -1), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 3)}, 10⟩
theorem entry_357_checked : entryAt 357 = entry_357 := by
  rw [entry_chunk_17 11 (by decide)]
  decide +kernel
theorem row_357 : rowAt 357 = data_357 := by
  rw [rowAt, dif_neg (by decide : ¬ 357 < 6), entry_357_checked]
  change forkRow [placeRow ⟨82, 6, 2, 3⟩ (rowAt 82), placeRow ⟨283, 0, 5, 6⟩ (rowAt 283)] = data_357
  rw [row_82, row_283]
  apply row_ext <;> decide +kernel
theorem entry_good_357 : EntryGood 357 := by
  unfold EntryGood
  rw [entry_357_checked]
  decide +kernel
theorem good_357 : Good (rowAt 357) := by
  rw [row_357]
  unfold Good
  decide +kernel

def data_358 : RowData := ⟨{(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)}, {(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)}, 11⟩
theorem entry_358_checked : entryAt 358 = entry_358 := by
  rw [entry_chunk_17 12 (by decide)]
  decide +kernel
theorem row_358 : rowAt 358 = data_358 := by
  rw [rowAt, dif_neg (by decide : ¬ 358 < 6), entry_358_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨346, 0, 4, 6⟩ (rowAt 346)] = data_358
  rw [row_6, row_346]
  apply row_ext <;> decide +kernel
theorem entry_good_358 : EntryGood 358 := by
  unfold EntryGood
  rw [entry_358_checked]
  decide +kernel
theorem good_358 : Good (rowAt 358) := by
  rw [row_358]
  unfold Good
  decide +kernel

def data_359 : RowData := ⟨{(-1, -1), (-1, 1), (0, -1), (0, 1)}, {(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)}, 9⟩
theorem entry_359_checked : entryAt 359 = entry_359 := by
  rw [entry_chunk_17 13 (by decide)]
  decide +kernel
theorem row_359 : rowAt 359 = data_359 := by
  rw [rowAt, dif_neg (by decide : ¬ 359 < 6), entry_359_checked]
  change forkRow [placeRow ⟨134, 0, 4, 6⟩ (rowAt 134), placeRow ⟨24, 7, 3, 2⟩ (rowAt 24), placeRow ⟨323, 0, 5, 5⟩ (rowAt 323)] = data_359
  rw [row_134, row_24, row_323]
  apply row_ext <;> decide +kernel
theorem entry_good_359 : EntryGood 359 := by
  unfold EntryGood
  rw [entry_359_checked]
  decide +kernel
theorem good_359 : Good (rowAt 359) := by
  rw [row_359]
  unfold Good
  decide +kernel

def data_360 : RowData := ⟨{(-2, -2), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-3, -1), (-2, -2), (-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (3, -3), (3, -2), (3, -1), (4, -3), (4, -2), (4, -1), (5, -3), (5, -1)}, 10⟩
theorem entry_360_checked : entryAt 360 = entry_360 := by
  rw [entry_chunk_17 14 (by decide)]
  decide +kernel
theorem row_360 : rowAt 360 = data_360 := by
  rw [rowAt, dif_neg (by decide : ¬ 360 < 6), entry_360_checked]
  change forkRow [placeRow ⟨155, 4, 4, 5⟩ (rowAt 155), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨337, 0, 5, 2⟩ (rowAt 337), placeRow ⟨228, 4, 5, 2⟩ (rowAt 228)] = data_360
  rw [row_155, row_7, row_337, row_228]
  apply row_ext <;> decide +kernel
theorem entry_good_360 : EntryGood 360 := by
  unfold EntryGood
  rw [entry_360_checked]
  decide +kernel
theorem good_360 : Good (rowAt 360) := by
  rw [row_360]
  unfold Good
  decide +kernel

def data_361 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (2, -1), (3, -1), (3, 0)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3)}, 12⟩
theorem entry_361_checked : entryAt 361 = entry_361 := by
  rw [entry_chunk_17 15 (by decide)]
  decide +kernel
theorem row_361 : rowAt 361 = data_361 := by
  rw [rowAt, dif_neg (by decide : ¬ 361 < 6), entry_361_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨352, 0, 4, 5⟩ (rowAt 352)] = data_361
  rw [row_6, row_352]
  apply row_ext <;> decide +kernel
theorem entry_good_361 : EntryGood 361 := by
  unfold EntryGood
  rw [entry_361_checked]
  decide +kernel
theorem good_361 : Good (rowAt 361) := by
  rw [row_361]
  unfold Good
  decide +kernel

def data_362 : RowData := ⟨{(-4, -1), (-3, -1), (-3, 2), (-2, -1), (-1, -1), (-1, 2)}, {(-6, 3), (-5, 2), (-5, 3), (-4, -1), (-4, 2), (-4, 3), (-3, -1), (-3, 2), (-3, 3), (-2, -1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)}, 11⟩
theorem entry_362_checked : entryAt 362 = entry_362 := by
  rw [entry_chunk_17 16 (by decide)]
  decide +kernel
theorem row_362 : rowAt 362 = data_362 := by
  rw [rowAt, dif_neg (by decide : ¬ 362 < 6), entry_362_checked]
  change forkRow [placeRow ⟨4, 0, 3, 4⟩ (rowAt 4), placeRow ⟨345, 0, 4, 3⟩ (rowAt 345)] = data_362
  rw [row_4, row_345]
  apply row_ext <;> decide +kernel
theorem entry_good_362 : EntryGood 362 := by
  unfold EntryGood
  rw [entry_362_checked]
  decide +kernel
theorem good_362 : Good (rowAt 362) := by
  rw [row_362]
  unfold Good
  decide +kernel

def data_363 : RowData := ⟨{(-4, -3), (-3, -3), (-3, 0), (-2, -3), (-1, -3), (-1, 0)}, {(-5, -1), (-4, -3), (-4, -1), (-4, 0), (-3, -3), (-3, -1), (-3, 0), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)}, 9⟩
theorem entry_363_checked : entryAt 363 = entry_363 := by
  rw [entry_chunk_17 17 (by decide)]
  decide +kernel
theorem row_363 : rowAt 363 = data_363 := by
  rw [rowAt, dif_neg (by decide : ¬ 363 < 6), entry_363_checked]
  change forkRow [placeRow ⟨137, 1, 4, 2⟩ (rowAt 137), placeRow ⟨248, 0, 2, 4⟩ (rowAt 248)] = data_363
  rw [row_137, row_248]
  apply row_ext <;> decide +kernel
theorem entry_good_363 : EntryGood 363 := by
  unfold EntryGood
  rw [entry_363_checked]
  decide +kernel
theorem good_363 : Good (rowAt 363) := by
  rw [row_363]
  unfold Good
  decide +kernel

def data_364 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-4, -4), (-4, -2), (-3, -4), (-3, -3), (-3, -2), (-2, -4), (-2, -3), (-2, -2), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -3), (4, -2), (5, -2)}, 10⟩
theorem entry_364_checked : entryAt 364 = entry_364 := by
  rw [entry_chunk_17 18 (by decide)]
  decide +kernel
theorem row_364 : rowAt 364 = data_364 := by
  rw [rowAt, dif_neg (by decide : ¬ 364 < 6), entry_364_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨314, 2, 3, 1⟩ (rowAt 314)] = data_364
  rw [row_63, row_314]
  apply row_ext <;> decide +kernel
theorem entry_good_364 : EntryGood 364 := by
  unfold EntryGood
  rw [entry_364_checked]
  decide +kernel
theorem good_364 : Good (rowAt 364) := by
  rw [row_364]
  unfold Good
  decide +kernel

def data_365 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (1, -3)}, {(-3, -1), (-2, -2), (-2, -1), (-2, 2), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1)}, 12⟩
theorem entry_365_checked : entryAt 365 = entry_365 := by
  rw [entry_chunk_17 19 (by decide)]
  decide +kernel
theorem row_365 : rowAt 365 = data_365 := by
  rw [rowAt, dif_neg (by decide : ¬ 365 < 6), entry_365_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨354, 0, 4, 3⟩ (rowAt 354)] = data_365
  rw [row_6, row_354]
  apply row_ext <;> decide +kernel
theorem entry_good_365 : EntryGood 365 := by
  unfold EntryGood
  rw [entry_365_checked]
  decide +kernel
theorem good_365 : Good (rowAt 365) := by
  rw [row_365]
  unfold Good
  decide +kernel

def data_366 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, 0)}, {(-2, -3), (-1, -3), (-1, -1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 1)}, 11⟩
theorem entry_366_checked : entryAt 366 = entry_366 := by
  rw [entry_chunk_18 0 (by decide)]
  decide +kernel
theorem row_366 : rowAt 366 = data_366 := by
  rw [rowAt, dif_neg (by decide : ¬ 366 < 6), entry_366_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨357, 0, 6, 2⟩ (rowAt 357)] = data_366
  rw [row_6, row_357]
  apply row_ext <;> decide +kernel
theorem entry_good_366 : EntryGood 366 := by
  unfold EntryGood
  rw [entry_366_checked]
  decide +kernel
theorem good_366 : Good (rowAt 366) := by
  rw [row_366]
  unfold Good
  decide +kernel

def data_367 : RowData := ⟨{(-3, 1), (-3, 2), (-2, 1), (-1, 1), (0, 1)}, {(-4, 3), (-4, 4), (-4, 5), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)}, 13⟩
theorem entry_367_checked : entryAt 367 = entry_367 := by
  rw [entry_chunk_18 1 (by decide)]
  decide +kernel
theorem row_367 : rowAt 367 = data_367 := by
  rw [rowAt, dif_neg (by decide : ¬ 367 < 6), entry_367_checked]
  change forkRow [placeRow ⟨6, 2, 5, 4⟩ (rowAt 6), placeRow ⟨361, 4, 4, 6⟩ (rowAt 361)] = data_367
  rw [row_6, row_361]
  apply row_ext <;> decide +kernel
theorem entry_good_367 : EntryGood 367 := by
  unfold EntryGood
  rw [entry_367_checked]
  decide +kernel
theorem good_367 : Good (rowAt 367) := by
  rw [row_367]
  unfold Good
  decide +kernel

def data_368 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-4, -3), (-3, -3), (-3, -1), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1)}, 12⟩
theorem entry_368_checked : entryAt 368 = entry_368 := by
  rw [entry_chunk_18 2 (by decide)]
  decide +kernel
theorem row_368 : rowAt 368 = data_368 := by
  rw [rowAt, dif_neg (by decide : ¬ 368 < 6), entry_368_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨366, 0, 2, 4⟩ (rowAt 366)] = data_368
  rw [row_6, row_366]
  apply row_ext <;> decide +kernel
theorem entry_good_368 : EntryGood 368 := by
  unfold EntryGood
  rw [entry_368_checked]
  decide +kernel
theorem good_368 : Good (rowAt 368) := by
  rw [row_368]
  unfold Good
  decide +kernel

def data_369 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (0, -1)}, {(-4, -2), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3)}, 14⟩
theorem entry_369_checked : entryAt 369 = entry_369 := by
  rw [entry_chunk_18 3 (by decide)]
  decide +kernel
theorem row_369 : rowAt 369 = data_369 := by
  rw [rowAt, dif_neg (by decide : ¬ 369 < 6), entry_369_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨367, 4, 1, 2⟩ (rowAt 367)] = data_369
  rw [row_6, row_367]
  apply row_ext <;> decide +kernel
theorem entry_good_369 : EntryGood 369 := by
  unfold EntryGood
  rw [entry_369_checked]
  decide +kernel
theorem good_369 : Good (rowAt 369) := by
  rw [row_369]
  unfold Good
  decide +kernel

def data_370 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 2), (4, 2)}, 11⟩
theorem entry_370_checked : entryAt 370 = entry_370 := by
  rw [entry_chunk_18 4 (by decide)]
  decide +kernel
theorem row_370 : rowAt 370 = data_370 := by
  rw [rowAt, dif_neg (by decide : ¬ 370 < 6), entry_370_checked]
  change forkRow [placeRow ⟨199, 3, 1, 4⟩ (rowAt 199), placeRow ⟨286, 1, 5, 4⟩ (rowAt 286), placeRow ⟨24, 6, 1, 3⟩ (rowAt 24), placeRow ⟨319, 0, 5, 3⟩ (rowAt 319)] = data_370
  rw [row_199, row_286, row_24, row_319]
  apply row_ext <;> decide +kernel
theorem entry_good_370 : EntryGood 370 := by
  unfold EntryGood
  rw [entry_370_checked]
  decide +kernel
theorem good_370 : Good (rowAt 370) := by
  rw [row_370]
  unfold Good
  decide +kernel

def data_371 : RowData := ⟨{(-4, -3), (-3, -3), (-3, 0), (-2, -3), (-1, -3), (-1, 0)}, {(-6, 1), (-5, 0), (-5, 1), (-4, -3), (-4, 0), (-4, 1), (-3, -3), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)}, 9⟩
theorem entry_371_checked : entryAt 371 = entry_371 := by
  rw [entry_chunk_18 5 (by decide)]
  decide +kernel
theorem row_371 : rowAt 371 = data_371 := by
  rw [rowAt, dif_neg (by decide : ¬ 371 < 6), entry_371_checked]
  change forkRow [placeRow ⟨267, 6, 2, 4⟩ (rowAt 267), placeRow ⟨137, 1, 4, 2⟩ (rowAt 137)] = data_371
  rw [row_267, row_137]
  apply row_ext <;> decide +kernel
theorem entry_good_371 : EntryGood 371 := by
  unfold EntryGood
  rw [entry_371_checked]
  decide +kernel
theorem good_371 : Good (rowAt 371) := by
  rw [row_371]
  unfold Good
  decide +kernel

def data_372 : RowData := ⟨{(-2, -3), (-2, -2), (-1, -4), (-1, -3), (-1, -2)}, {(-5, 1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 11⟩
theorem entry_372_checked : entryAt 372 = entry_372 := by
  rw [entry_chunk_18 6 (by decide)]
  decide +kernel
theorem row_372 : rowAt 372 = data_372 := by
  rw [rowAt, dif_neg (by decide : ¬ 372 < 6), entry_372_checked]
  change forkRow [placeRow ⟨40, 1, 4, 3⟩ (rowAt 40), placeRow ⟨333, 0, 2, 4⟩ (rowAt 333), placeRow ⟨120, 1, 3, 3⟩ (rowAt 120), placeRow ⟨161, 0, 4, 2⟩ (rowAt 161)] = data_372
  rw [row_40, row_333, row_120, row_161]
  apply row_ext <;> decide +kernel
theorem entry_good_372 : EntryGood 372 := by
  unfold EntryGood
  rw [entry_372_checked]
  decide +kernel
theorem good_372 : Good (rowAt 372) := by
  rw [row_372]
  unfold Good
  decide +kernel

def data_373 : RowData := ⟨{(-1, -1), (0, -1), (0, 1), (2, -1), (2, 0), (2, 1)}, {(-5, 0), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0)}, 9⟩
theorem entry_373_checked : entryAt 373 = entry_373 := by
  rw [entry_chunk_18 7 (by decide)]
  decide +kernel
theorem row_373 : rowAt 373 = data_373 := by
  rw [rowAt, dif_neg (by decide : ¬ 373 < 6), entry_373_checked]
  change forkRow [placeRow ⟨156, 2, 7, 4⟩ (rowAt 156), placeRow ⟨226, 4, 3, 5⟩ (rowAt 226), placeRow ⟨80, 0, 5, 4⟩ (rowAt 80), placeRow ⟨327, 0, 5, 5⟩ (rowAt 327), placeRow ⟨156, 6, 3, 4⟩ (rowAt 156)] = data_373
  rw [row_156, row_226, row_80, row_327]
  apply row_ext <;> decide +kernel
theorem entry_good_373 : EntryGood 373 := by
  unfold EntryGood
  rw [entry_373_checked]
  decide +kernel
theorem good_373 : Good (rowAt 373) := by
  rw [row_373]
  unfold Good
  decide +kernel

def data_374 : RowData := ⟨{(1, -2), (1, 0), (2, -1), (2, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)}, 10⟩
theorem entry_374_checked : entryAt 374 = entry_374 := by
  rw [entry_chunk_18 8 (by decide)]
  decide +kernel
theorem row_374 : rowAt 374 = data_374 := by
  rw [rowAt, dif_neg (by decide : ¬ 374 < 6), entry_374_checked]
  change forkRow [placeRow ⟨65, 4, 3, 4⟩ (rowAt 65), placeRow ⟨335, 0, 7, 4⟩ (rowAt 335), placeRow ⟨24, 2, 7, 3⟩ (rowAt 24), placeRow ⟨163, 4, 3, 4⟩ (rowAt 163)] = data_374
  rw [row_65, row_335, row_24, row_163]
  apply row_ext <;> decide +kernel
theorem entry_good_374 : EntryGood 374 := by
  unfold EntryGood
  rw [entry_374_checked]
  decide +kernel
theorem good_374 : Good (rowAt 374) := by
  rw [row_374]
  unfold Good
  decide +kernel

def data_375 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 1), (0, -1), (0, 1)}, {(-7, 0), (-6, -2), (-6, -1), (-6, 0), (-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, 0)}, 9⟩
theorem entry_375_checked : entryAt 375 = entry_375 := by
  rw [entry_chunk_18 9 (by decide)]
  decide +kernel
theorem row_375 : rowAt 375 = data_375 := by
  rw [rowAt, dif_neg (by decide : ¬ 375 < 6), entry_375_checked]
  change forkRow [placeRow ⟨24, 3, 3, 6⟩ (rowAt 24), placeRow ⟨327, 6, 3, 3⟩ (rowAt 327)] = data_375
  rw [row_24, row_327]
  apply row_ext <;> decide +kernel
theorem entry_good_375 : EntryGood 375 := by
  unfold EntryGood
  rw [entry_375_checked]
  decide +kernel
theorem good_375 : Good (rowAt 375) := by
  rw [row_375]
  unfold Good
  decide +kernel

def data_376 : RowData := ⟨{(-3, 0), (-2, 0), (-1, -1), (-1, 0)}, {(-6, 2), (-5, 2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 10⟩
theorem entry_376_checked : entryAt 376 = entry_376 := by
  rw [entry_chunk_18 10 (by decide)]
  decide +kernel
theorem row_376 : rowAt 376 = data_376 := by
  rw [rowAt, dif_neg (by decide : ¬ 376 < 6), entry_376_checked]
  change forkRow [placeRow ⟨162, 1, 5, 4⟩ (rowAt 162), placeRow ⟨285, 3, 1, 3⟩ (rowAt 285)] = data_376
  rw [row_162, row_285]
  apply row_ext <;> decide +kernel
theorem entry_good_376 : EntryGood 376 := by
  unfold EntryGood
  rw [entry_376_checked]
  decide +kernel
theorem good_376 : Good (rowAt 376) := by
  rw [row_376]
  unfold Good
  decide +kernel

def data_377 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3), (2, 0)}, {(-3, 1), (-2, -4), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, 0), (1, 1), (2, -4), (2, -3), (2, -2), (2, 0), (2, 1), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 12⟩
theorem entry_377_checked : entryAt 377 = entry_377 := by
  rw [entry_chunk_18 11 (by decide)]
  decide +kernel
theorem row_377 : rowAt 377 = data_377 := by
  rw [rowAt, dif_neg (by decide : ¬ 377 < 6), entry_377_checked]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (rowAt 29), placeRow ⟨362, 0, 7, 2⟩ (rowAt 362)] = data_377
  rw [row_29, row_362]
  apply row_ext <;> decide +kernel
theorem entry_good_377 : EntryGood 377 := by
  unfold EntryGood
  rw [entry_377_checked]
  decide +kernel
theorem good_377 : Good (rowAt 377) := by
  rw [row_377]
  unfold Good
  decide +kernel

def data_378 : RowData := ⟨{(-2, 0), (-1, -2), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1)}, 11⟩
theorem entry_378_checked : entryAt 378 = entry_378 := by
  rw [entry_chunk_18 12 (by decide)]
  decide +kernel
theorem row_378 : rowAt 378 = data_378 := by
  rw [rowAt, dif_neg (by decide : ¬ 378 < 6), entry_378_checked]
  change forkRow [placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨176, 4, 1, 4⟩ (rowAt 176), placeRow ⟨183, 4, 1, 4⟩ (rowAt 183), placeRow ⟨172, 6, 1, 4⟩ (rowAt 172), placeRow ⟨294, 4, 1, 4⟩ (rowAt 294)] = data_378
  rw [row_295, row_176, row_183, row_172, row_294]
  apply row_ext <;> decide +kernel
theorem entry_good_378 : EntryGood 378 := by
  unfold EntryGood
  rw [entry_378_checked]
  decide +kernel
theorem good_378 : Good (rowAt 378) := by
  rw [row_378]
  unfold Good
  decide +kernel

def data_379 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-3, -3), (-2, -3), (-2, -1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1)}, 13⟩
theorem entry_379_checked : entryAt 379 = entry_379 := by
  rw [entry_chunk_18 13 (by decide)]
  decide +kernel
theorem row_379 : rowAt 379 = data_379 := by
  rw [rowAt, dif_neg (by decide : ¬ 379 < 6), entry_379_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨64, 1, 3, 1⟩ (rowAt 64), placeRow ⟨55, 3, 4, 5⟩ (rowAt 55), placeRow ⟨368, 0, 5, 4⟩ (rowAt 368)] = data_379
  rw [row_63, row_64, row_55, row_368]
  apply row_ext <;> decide +kernel
theorem entry_good_379 : EntryGood 379 := by
  unfold EntryGood
  rw [entry_379_checked]
  decide +kernel
theorem good_379 : Good (rowAt 379) := by
  rw [row_379]
  unfold Good
  decide +kernel

def data_380 : RowData := ⟨{(-2, 0), (-2, 2), (-1, -1), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 8⟩
theorem entry_380_checked : entryAt 380 = entry_380 := by
  rw [entry_chunk_18 14 (by decide)]
  decide +kernel
theorem row_380 : rowAt 380 = data_380 := by
  rw [rowAt, dif_neg (by decide : ¬ 380 < 6), entry_380_checked]
  change forkRow [placeRow ⟨101, 4, 2, 5⟩ (rowAt 101), placeRow ⟨271, 0, 2, 5⟩ (rowAt 271), placeRow ⟨223, 0, 5, 4⟩ (rowAt 223), placeRow ⟨192, 3, 1, 4⟩ (rowAt 192)] = data_380
  rw [row_101, row_271, row_223, row_192]
  apply row_ext <;> decide +kernel
theorem entry_good_380 : EntryGood 380 := by
  unfold EntryGood
  rw [entry_380_checked]
  decide +kernel
theorem good_380 : Good (rowAt 380) := by
  rw [row_380]
  unfold Good
  decide +kernel

def data_381 : RowData := ⟨{(1, 0), (2, -1), (2, 0), (2, 1)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, 1)}, 10⟩
theorem entry_381_checked : entryAt 381 = entry_381 := by
  rw [entry_chunk_18 15 (by decide)]
  decide +kernel
theorem row_381 : rowAt 381 = data_381 := by
  rw [rowAt, dif_neg (by decide : ¬ 381 < 6), entry_381_checked]
  change forkRow [placeRow ⟨211, 6, 3, 4⟩ (rowAt 211), placeRow ⟨24, 0, 7, 5⟩ (rowAt 24), placeRow ⟨163, 4, 3, 4⟩ (rowAt 163), placeRow ⟨341, 0, 7, 4⟩ (rowAt 341)] = data_381
  rw [row_211, row_24, row_163, row_341]
  apply row_ext <;> decide +kernel
theorem entry_good_381 : EntryGood 381 := by
  unfold EntryGood
  rw [entry_381_checked]
  decide +kernel
theorem good_381 : Good (rowAt 381) := by
  rw [row_381]
  unfold Good
  decide +kernel

def data_382 : RowData := ⟨{(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2)}, {(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1)}, 5⟩
theorem entry_382_checked : entryAt 382 = entry_382 := by
  rw [entry_chunk_18 16 (by decide)]
  decide +kernel
theorem row_382 : rowAt 382 = data_382 := by
  rw [rowAt, dif_neg (by decide : ¬ 382 < 6), entry_382_checked]
  change forkRow [placeRow ⟨124, 1, 5, 3⟩ (rowAt 124), placeRow ⟨2, 7, 4, 3⟩ (rowAt 2)] = data_382
  rw [row_124, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_382 : EntryGood 382 := by
  unfold EntryGood
  rw [entry_382_checked]
  decide +kernel
theorem good_382 : Good (rowAt 382) := by
  rw [row_382]
  unfold Good
  decide +kernel

def data_383 : RowData := ⟨{(-1, 0), (-1, 2), (1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 8⟩
theorem entry_383_checked : entryAt 383 = entry_383 := by
  rw [entry_chunk_18 17 (by decide)]
  decide +kernel
theorem row_383 : rowAt 383 = data_383 := by
  rw [rowAt, dif_neg (by decide : ¬ 383 < 6), entry_383_checked]
  change forkRow [placeRow ⟨192, 3, 2, 4⟩ (rowAt 192), placeRow ⟨271, 0, 3, 5⟩ (rowAt 271), placeRow ⟨197, 0, 6, 4⟩ (rowAt 197), placeRow ⟨172, 0, 6, 4⟩ (rowAt 172), placeRow ⟨215, 4, 3, 5⟩ (rowAt 215)] = data_383
  rw [row_192, row_271, row_197, row_172, row_215]
  apply row_ext <;> decide +kernel
theorem entry_good_383 : EntryGood 383 := by
  unfold EntryGood
  rw [entry_383_checked]
  decide +kernel
theorem good_383 : Good (rowAt 383) := by
  rw [row_383]
  unfold Good
  decide +kernel

#check row_383
def data_384 : RowData := ⟨{(-1, 0), (1, 0)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)}, 11⟩
theorem entry_384_checked : entryAt 384 = entry_384 := by
  rw [entry_chunk_18 18 (by decide)]
  decide +kernel
theorem row_384 : rowAt 384 = data_384 := by
  rw [rowAt, dif_neg (by decide : ¬ 384 < 6), entry_384_checked]
  change forkRow [placeRow ⟨173, 2, 6, 4⟩ (rowAt 173), placeRow ⟨282, 4, 2, 4⟩ (rowAt 282), placeRow ⟨220, 2, 6, 4⟩ (rowAt 220), placeRow ⟨246, 2, 6, 4⟩ (rowAt 246), placeRow ⟨263, 2, 6, 4⟩ (rowAt 263), placeRow ⟨183, 6, 2, 4⟩ (rowAt 183), placeRow ⟨295, 0, 6, 4⟩ (rowAt 295)] = data_384
  rw [row_173, row_282, row_220, row_246, row_263, row_183, row_295]
  apply row_ext <;> decide +kernel
theorem entry_good_384 : EntryGood 384 := by
  unfold EntryGood
  rw [entry_384_checked]
  decide +kernel
theorem good_384 : Good (rowAt 384) := by
  rw [row_384]
  unfold Good
  decide +kernel

def data_385 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 1)}, 15⟩
theorem entry_385_checked : entryAt 385 = entry_385 := by
  rw [entry_chunk_18 19 (by decide)]
  decide +kernel
theorem row_385 : rowAt 385 = data_385 := by
  rw [rowAt, dif_neg (by decide : ¬ 385 < 6), entry_385_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨369, 4, 1, 5⟩ (rowAt 369)] = data_385
  rw [row_63, row_64, row_55, row_369]
  apply row_ext <;> decide +kernel
theorem entry_good_385 : EntryGood 385 := by
  unfold EntryGood
  rw [entry_385_checked]
  decide +kernel
theorem good_385 : Good (rowAt 385) := by
  rw [row_385]
  unfold Good
  decide +kernel

def data_386 : RowData := ⟨{(-2, 0), (-1, -2), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 10⟩
theorem entry_386_checked : entryAt 386 = entry_386 := by
  rw [entry_chunk_19 0 (by decide)]
  decide +kernel
theorem row_386 : rowAt 386 = data_386 := by
  rw [rowAt, dif_neg (by decide : ¬ 386 < 6), entry_386_checked]
  change forkRow [placeRow ⟨217, 4, 1, 4⟩ (rowAt 217), placeRow ⟨172, 0, 5, 4⟩ (rowAt 172), placeRow ⟨173, 4, 1, 4⟩ (rowAt 173), placeRow ⟨217, 0, 5, 4⟩ (rowAt 217), placeRow ⟨294, 0, 5, 4⟩ (rowAt 294), placeRow ⟨294, 4, 1, 4⟩ (rowAt 294)] = data_386
  rw [row_217, row_172, row_173, row_294]
  apply row_ext <;> decide +kernel
theorem entry_good_386 : EntryGood 386 := by
  unfold EntryGood
  rw [entry_386_checked]
  decide +kernel
theorem good_386 : Good (rowAt 386) := by
  rw [row_386]
  unfold Good
  decide +kernel

def data_387 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0), (0, 1)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 2), (5, 2)}, 12⟩
theorem entry_387_checked : entryAt 387 = entry_387 := by
  rw [entry_chunk_19 1 (by decide)]
  decide +kernel
theorem row_387 : rowAt 387 = data_387 := by
  rw [rowAt, dif_neg (by decide : ¬ 387 < 6), entry_387_checked]
  change forkRow [placeRow ⟨14, 1, 4, 6⟩ (rowAt 14), placeRow ⟨370, 0, 5, 4⟩ (rowAt 370)] = data_387
  rw [row_14, row_370]
  apply row_ext <;> decide +kernel
theorem entry_good_387 : EntryGood 387 := by
  unfold EntryGood
  rw [entry_387_checked]
  decide +kernel
theorem good_387 : Good (rowAt 387) := by
  rw [row_387]
  unfold Good
  decide +kernel

def data_388 : RowData := ⟨{(0, -2), (1, -3), (1, -2), (1, -1), (1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 11⟩
theorem entry_388_checked : entryAt 388 = entry_388 := by
  rw [entry_chunk_19 2 (by decide)]
  decide +kernel
theorem row_388 : rowAt 388 = data_388 := by
  rw [rowAt, dif_neg (by decide : ¬ 388 < 6), entry_388_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨374, 0, 3, 4⟩ (rowAt 374)] = data_388
  rw [row_6, row_374]
  apply row_ext <;> decide +kernel
theorem entry_good_388 : EntryGood 388 := by
  unfold EntryGood
  rw [entry_388_checked]
  decide +kernel
theorem good_388 : Good (rowAt 388) := by
  rw [row_388]
  unfold Good
  decide +kernel

def data_389 : RowData := ⟨{(-2, -2), (0, -2), (0, -1)}, {(-5, -3), (-5, -1), (-4, -3), (-4, -2), (-4, -1), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, 0), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, 0), (2, 1), (3, 1), (4, 1)}, 8⟩
theorem entry_389_checked : entryAt 389 = entry_389 := by
  rw [entry_chunk_19 3 (by decide)]
  decide +kernel
theorem row_389 : rowAt 389 = data_389 := by
  rw [rowAt, dif_neg (by decide : ¬ 389 < 6), entry_389_checked]
  change forkRow [placeRow ⟨197, 5, 4, 1⟩ (rowAt 197), placeRow ⟨215, 7, 3, 2⟩ (rowAt 215), placeRow ⟨271, 3, 3, 2⟩ (rowAt 271), placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨192, 6, 4, 1⟩ (rowAt 192)] = data_389
  rw [row_197, row_215, row_271, row_236, row_192]
  apply row_ext <;> decide +kernel
theorem entry_good_389 : EntryGood 389 := by
  unfold EntryGood
  rw [entry_389_checked]
  decide +kernel
theorem good_389 : Good (rowAt 389) := by
  rw [row_389]
  unfold Good
  decide +kernel

def data_390 : RowData := ⟨{(-1, -2), (-1, -1), (0, -2), (0, -1)}, {(-4, -5), (-3, -5), (-3, -4), (-2, -5), (-2, -4), (-2, -3), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -5), (2, -4), (2, -2), (3, -5), (3, -4), (3, -3), (3, -2), (4, -5), (4, -4), (4, -3), (5, -5), (5, -4), (5, -3)}, 12⟩
theorem entry_390_checked : entryAt 390 = entry_390 := by
  rw [entry_chunk_19 4 (by decide)]
  decide +kernel
theorem row_390 : rowAt 390 = data_390 := by
  rw [rowAt, dif_neg (by decide : ¬ 390 < 6), entry_390_checked]
  change forkRow [placeRow ⟨372, 2, 5, 0⟩ (rowAt 372), placeRow ⟨167, 5, 4, 1⟩ (rowAt 167), placeRow ⟨12, 7, 3, 1⟩ (rowAt 12)] = data_390
  rw [row_372, row_167, row_12]
  apply row_ext <;> decide +kernel
theorem entry_good_390 : EntryGood 390 := by
  unfold EntryGood
  rw [entry_390_checked]
  decide +kernel
theorem good_390 : Good (rowAt 390) := by
  rw [row_390]
  unfold Good
  decide +kernel

def data_391 : RowData := ⟨{(-1, -1), (0, -2), (0, -1), (0, 1), (1, -2)}, {(-5, 0), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)}, 12⟩
theorem entry_391_checked : entryAt 391 = entry_391 := by
  rw [entry_chunk_19 5 (by decide)]
  decide +kernel
theorem row_391 : rowAt 391 = data_391 := by
  rw [rowAt, dif_neg (by decide : ¬ 391 < 6), entry_391_checked]
  change forkRow [placeRow ⟨6, 5, 5, 1⟩ (rowAt 6), placeRow ⟨388, 0, 3, 5⟩ (rowAt 388)] = data_391
  rw [row_6, row_388]
  apply row_ext <;> decide +kernel
theorem entry_good_391 : EntryGood 391 := by
  unfold EntryGood
  rw [entry_391_checked]
  decide +kernel
theorem good_391 : Good (rowAt 391) := by
  rw [row_391]
  unfold Good
  decide +kernel

def data_392 : RowData := ⟨{(-1, -2), (0, -2), (0, -1)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 11⟩
theorem entry_392_checked : entryAt 392 = entry_392 := by
  rw [entry_chunk_19 6 (by decide)]
  decide +kernel
theorem row_392 : rowAt 392 = data_392 := by
  rw [rowAt, dif_neg (by decide : ¬ 392 < 6), entry_392_checked]
  change forkRow [placeRow ⟨24, 7, 3, 1⟩ (rowAt 24), placeRow ⟨107, 1, 4, 5⟩ (rowAt 107), placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨364, 2, 4, 1⟩ (rowAt 364)] = data_392
  rw [row_24, row_107, row_236, row_364]
  apply row_ext <;> decide +kernel
theorem entry_good_392 : EntryGood 392 := by
  unfold EntryGood
  rw [entry_392_checked]
  decide +kernel
theorem good_392 : Good (rowAt 392) := by
  rw [row_392]
  unfold Good
  decide +kernel

def data_393 : RowData := ⟨{(0, -2), (0, -1), (1, -2), (2, -3), (2, -2), (3, -2), (3, -1)}, {(-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 12⟩
theorem entry_393_checked : entryAt 393 = entry_393 := by
  rw [entry_chunk_19 7 (by decide)]
  decide +kernel
theorem row_393 : rowAt 393 = data_393 := by
  rw [rowAt, dif_neg (by decide : ¬ 393 < 6), entry_393_checked]
  change forkRow [placeRow ⟨107, 3, 4, 5⟩ (rowAt 107), placeRow ⟨348, 0, 6, 3⟩ (rowAt 348), placeRow ⟨65, 3, 4, 5⟩ (rowAt 65), placeRow ⟨303, 0, 4, 5⟩ (rowAt 303)] = data_393
  rw [row_107, row_348, row_65, row_303]
  apply row_ext <;> decide +kernel
theorem entry_good_393 : EntryGood 393 := by
  unfold EntryGood
  rw [entry_393_checked]
  decide +kernel
theorem good_393 : Good (rowAt 393) := by
  rw [row_393]
  unfold Good
  decide +kernel

def data_394 : RowData := ⟨{(-2, -1), (-2, 0), (0, -1)}, {(-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, -1), (5, 0), (5, 1)}, 9⟩
theorem entry_394_checked : entryAt 394 = entry_394 := by
  rw [entry_chunk_19 8 (by decide)]
  decide +kernel
theorem row_394 : rowAt 394 = data_394 := by
  rw [rowAt, dif_neg (by decide : ¬ 394 < 6), entry_394_checked]
  change forkRow [placeRow ⟨226, 4, 1, 4⟩ (rowAt 226), placeRow ⟨226, 0, 5, 4⟩ (rowAt 226), placeRow ⟨327, 4, 3, 4⟩ (rowAt 327), placeRow ⟨327, 6, 3, 3⟩ (rowAt 327), placeRow ⟨226, 6, 1, 3⟩ (rowAt 226), placeRow ⟨226, 2, 5, 3⟩ (rowAt 226)] = data_394
  rw [row_226, row_327]
  apply row_ext <;> decide +kernel
theorem entry_good_394 : EntryGood 394 := by
  unfold EntryGood
  rw [entry_394_checked]
  decide +kernel
theorem good_394 : Good (rowAt 394) := by
  rw [row_394]
  unfold Good
  decide +kernel

def data_395 : RowData := ⟨{(-1, 0), (1, -1), (1, 0), (1, 1)}, {(-4, -1), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 11⟩
theorem entry_395_checked : entryAt 395 = entry_395 := by
  rw [entry_chunk_19 9 (by decide)]
  decide +kernel
theorem row_395 : rowAt 395 = data_395 := by
  rw [rowAt, dif_neg (by decide : ¬ 395 < 6), entry_395_checked]
  change forkRow [placeRow ⟨211, 4, 2, 4⟩ (rowAt 211), placeRow ⟨376, 0, 6, 4⟩ (rowAt 376), placeRow ⟨24, 2, 6, 3⟩ (rowAt 24), placeRow ⟨236, 3, 2, 5⟩ (rowAt 236)] = data_395
  rw [row_211, row_376, row_24, row_236]
  apply row_ext <;> decide +kernel
theorem entry_good_395 : EntryGood 395 := by
  unfold EntryGood
  rw [entry_395_checked]
  decide +kernel
theorem good_395 : Good (rowAt 395) := by
  rw [row_395]
  unfold Good
  decide +kernel

def data_396 : RowData := ⟨{(0, -2), (0, -1), (1, -2), (2, -2), (3, -2)}, {(-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 13⟩
theorem entry_396_checked : entryAt 396 = entry_396 := by
  rw [entry_chunk_19 10 (by decide)]
  decide +kernel
theorem row_396 : rowAt 396 = data_396 := by
  rw [rowAt, dif_neg (by decide : ¬ 396 < 6), entry_396_checked]
  change forkRow [placeRow ⟨107, 3, 4, 5⟩ (rowAt 107), placeRow ⟨365, 1, 7, 3⟩ (rowAt 365), placeRow ⟨303, 0, 4, 5⟩ (rowAt 303), placeRow ⟨65, 3, 4, 5⟩ (rowAt 65)] = data_396
  rw [row_107, row_365, row_303, row_65]
  apply row_ext <;> decide +kernel
theorem entry_good_396 : EntryGood 396 := by
  unfold EntryGood
  rw [entry_396_checked]
  decide +kernel
theorem good_396 : Good (rowAt 396) := by
  rw [row_396]
  unfold Good
  decide +kernel

def data_397 : RowData := ⟨{(0, -2), (1, -2), (1, -1), (1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -5), (2, -4), (2, -3), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 11⟩
theorem entry_397_checked : entryAt 397 = entry_397 := by
  rw [entry_chunk_19 11 (by decide)]
  decide +kernel
theorem row_397 : rowAt 397 = data_397 := by
  rw [rowAt, dif_neg (by decide : ¬ 397 < 6), entry_397_checked]
  change forkRow [placeRow ⟨24, 3, 4, 5⟩ (rowAt 24), placeRow ⟨374, 0, 3, 4⟩ (rowAt 374), placeRow ⟨65, 5, 5, 1⟩ (rowAt 65)] = data_397
  rw [row_24, row_374, row_65]
  apply row_ext <;> decide +kernel
theorem entry_good_397 : EntryGood 397 := by
  unfold EntryGood
  rw [entry_397_checked]
  decide +kernel
theorem good_397 : Good (rowAt 397) := by
  rw [row_397]
  unfold Good
  decide +kernel

def data_398 : RowData := ⟨{(-3, -4), (-3, -3), (-3, -2), (-2, -3), (-2, 0), (-1, -3), (0, -3)}, {(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 10⟩
theorem entry_398_checked : entryAt 398 = entry_398 := by
  rw [entry_chunk_19 12 (by decide)]
  decide +kernel
theorem row_398 : rowAt 398 = data_398 := by
  rw [rowAt, dif_neg (by decide : ¬ 398 < 6), entry_398_checked]
  change forkRow [placeRow ⟨257, 0, 1, 3⟩ (rowAt 257), placeRow ⟨363, 0, 5, 4⟩ (rowAt 363), placeRow ⟨130, 1, 4, 2⟩ (rowAt 130), placeRow ⟨177, 1, 4, 2⟩ (rowAt 177)] = data_398
  rw [row_257, row_363, row_130, row_177]
  apply row_ext <;> decide +kernel
theorem entry_good_398 : EntryGood 398 := by
  unfold EntryGood
  rw [entry_398_checked]
  decide +kernel
theorem good_398 : Good (rowAt 398) := by
  rw [row_398]
  unfold Good
  decide +kernel

def data_399 : RowData := ⟨{(-2, -2), (0, -2), (0, -1)}, {(-5, -3), (-5, -1), (-4, -3), (-4, -2), (-4, -1), (-3, -3), (-3, -2), (-3, -1), (-2, -2), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2)}, 11⟩
theorem entry_399_checked : entryAt 399 = entry_399 := by
  rw [entry_chunk_19 13 (by decide)]
  decide +kernel
theorem row_399 : rowAt 399 = data_399 := by
  rw [rowAt, dif_neg (by decide : ¬ 399 < 6), entry_399_checked]
  change forkRow [placeRow ⟨192, 6, 4, 1⟩ (rowAt 192), placeRow ⟨271, 3, 3, 2⟩ (rowAt 271), placeRow ⟨173, 1, 4, 5⟩ (rowAt 173), placeRow ⟨319, 1, 3, 5⟩ (rowAt 319), placeRow ⟨215, 7, 3, 2⟩ (rowAt 215)] = data_399
  rw [row_192, row_271, row_173, row_319, row_215]
  apply row_ext <;> decide +kernel
theorem entry_good_399 : EntryGood 399 := by
  unfold EntryGood
  rw [entry_399_checked]
  decide +kernel
theorem good_399 : Good (rowAt 399) := by
  rw [row_399]
  unfold Good
  decide +kernel

def data_400 : RowData := ⟨{(-1, -2), (-1, 0), (1, -2), (1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1)}, 10⟩
theorem entry_400_checked : entryAt 400 = entry_400 := by
  rw [entry_chunk_19 14 (by decide)]
  decide +kernel
theorem row_400 : rowAt 400 = data_400 := by
  rw [rowAt, dif_neg (by decide : ¬ 400 < 6), entry_400_checked]
  change forkRow [placeRow ⟨283, 4, 2, 4⟩ (rowAt 283), placeRow ⟨252, 4, 2, 4⟩ (rowAt 252), placeRow ⟨176, 4, 2, 4⟩ (rowAt 176), placeRow ⟨197, 0, 6, 4⟩ (rowAt 197), placeRow ⟨283, 0, 6, 4⟩ (rowAt 283), placeRow ⟨245, 4, 2, 4⟩ (rowAt 245)] = data_400
  rw [row_283, row_252, row_176, row_197, row_245]
  apply row_ext <;> decide +kernel
theorem entry_good_400 : EntryGood 400 := by
  unfold EntryGood
  rw [entry_400_checked]
  decide +kernel
theorem good_400 : Good (rowAt 400) := by
  rw [row_400]
  unfold Good
  decide +kernel

def data_401 : RowData := ⟨{(-1, -1), (0, -1), (0, 1)}, {(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0)}, 11⟩
theorem entry_401_checked : entryAt 401 = entry_401 := by
  rw [entry_chunk_19 15 (by decide)]
  decide +kernel
theorem row_401 : rowAt 401 = data_401 := by
  rw [rowAt, dif_neg (by decide : ¬ 401 < 6), entry_401_checked]
  change forkRow [placeRow ⟨24, 7, 3, 2⟩ (rowAt 24), placeRow ⟨286, 0, 4, 6⟩ (rowAt 286), placeRow ⟨364, 2, 4, 2⟩ (rowAt 364), placeRow ⟨319, 1, 3, 6⟩ (rowAt 319)] = data_401
  rw [row_24, row_286, row_364, row_319]
  apply row_ext <;> decide +kernel
theorem entry_good_401 : EntryGood 401 := by
  unfold EntryGood
  rw [entry_401_checked]
  decide +kernel
theorem good_401 : Good (rowAt 401) := by
  rw [row_401]
  unfold Good
  decide +kernel

def data_402 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3), (2, 0)}, {(-3, 1), (-2, -4), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 12⟩
theorem entry_402_checked : entryAt 402 = entry_402 := by
  rw [entry_chunk_19 16 (by decide)]
  decide +kernel
theorem row_402 : rowAt 402 = data_402 := by
  rw [rowAt, dif_neg (by decide : ¬ 402 < 6), entry_402_checked]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (rowAt 29), placeRow ⟨384, 0, 5, 4⟩ (rowAt 384)] = data_402
  rw [row_29, row_384]
  apply row_ext <;> decide +kernel
theorem entry_good_402 : EntryGood 402 := by
  unfold EntryGood
  rw [entry_402_checked]
  decide +kernel
theorem good_402 : Good (rowAt 402) := by
  rw [row_402]
  unfold Good
  decide +kernel

def data_403 : RowData := ⟨{(-1, -2), (0, -3), (0, -2), (0, -1)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 12⟩
theorem entry_403_checked : entryAt 403 = entry_403 := by
  rw [entry_chunk_19 17 (by decide)]
  decide +kernel
theorem row_403 : rowAt 403 = data_403 := by
  rw [rowAt, dif_neg (by decide : ¬ 403 < 6), entry_403_checked]
  change forkRow [placeRow ⟨202, 1, 4, 5⟩ (rowAt 202), placeRow ⟨180, 0, 4, 5⟩ (rowAt 180), placeRow ⟨314, 4, 5, 4⟩ (rowAt 314), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨388, 0, 3, 4⟩ (rowAt 388)] = data_403
  rw [row_202, row_180, row_314, row_63, row_388]
  apply row_ext <;> decide +kernel
theorem entry_good_403 : EntryGood 403 := by
  unfold EntryGood
  rw [entry_403_checked]
  decide +kernel
theorem good_403 : Good (rowAt 403) := by
  rw [row_403]
  unfold Good
  decide +kernel

def data_404 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (-1, 2)}, {(-6, 1), (-5, 1), (-5, 2), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)}, 12⟩
theorem entry_404_checked : entryAt 404 = entry_404 := by
  rw [entry_chunk_19 18 (by decide)]
  decide +kernel
theorem row_404 : rowAt 404 = data_404 := by
  rw [rowAt, dif_neg (by decide : ¬ 404 < 6), entry_404_checked]
  change forkRow [placeRow ⟨82, 6, 2, 3⟩ (rowAt 82), placeRow ⟨388, 4, 4, 6⟩ (rowAt 388)] = data_404
  rw [row_82, row_388]
  apply row_ext <;> decide +kernel
theorem entry_good_404 : EntryGood 404 := by
  unfold EntryGood
  rw [entry_404_checked]
  decide +kernel
theorem good_404 : Good (rowAt 404) := by
  rw [row_404]
  unfold Good
  decide +kernel

def data_405 : RowData := ⟨{(-2, -2), (-1, -3), (-1, -2), (0, -3), (0, -2), (1, -3)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 13⟩
theorem entry_405_checked : entryAt 405 = entry_405 := by
  rw [entry_chunk_19 19 (by decide)]
  decide +kernel
theorem row_405 : rowAt 405 = data_405 := by
  rw [rowAt, dif_neg (by decide : ¬ 405 < 6), entry_405_checked]
  change forkRow [placeRow ⟨391, 0, 4, 3⟩ (rowAt 391), placeRow ⟨301, 0, 5, 2⟩ (rowAt 301), placeRow ⟨42, 1, 4, 3⟩ (rowAt 42)] = data_405
  rw [row_391, row_301, row_42]
  apply row_ext <;> decide +kernel
theorem entry_good_405 : EntryGood 405 := by
  unfold EntryGood
  rw [entry_405_checked]
  decide +kernel
theorem good_405 : Good (rowAt 405) := by
  rw [row_405]
  unfold Good
  decide +kernel

def data_406 : RowData := ⟨{(0, -2), (0, -1)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1)}, 11⟩
theorem entry_406_checked : entryAt 406 = entry_406 := by
  rw [entry_chunk_20 0 (by decide)]
  decide +kernel
theorem row_406 : rowAt 406 = data_406 := by
  rw [rowAt, dif_neg (by decide : ¬ 406 < 6), entry_406_checked]
  change forkRow [placeRow ⟨295, 1, 4, 5⟩ (rowAt 295), placeRow ⟨172, 7, 4, 1⟩ (rowAt 172), placeRow ⟨245, 3, 4, 5⟩ (rowAt 245), placeRow ⟨197, 5, 4, 1⟩ (rowAt 197), placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨176, 3, 4, 5⟩ (rowAt 176), placeRow ⟨364, 2, 4, 1⟩ (rowAt 364)] = data_406
  rw [row_295, row_172, row_245, row_197, row_236, row_176, row_364]
  apply row_ext <;> decide +kernel
theorem entry_good_406 : EntryGood 406 := by
  unfold EntryGood
  rw [entry_406_checked]
  decide +kernel
theorem good_406 : Good (rowAt 406) := by
  rw [row_406]
  unfold Good
  decide +kernel

def data_407 : RowData := ⟨{(0, 1), (0, 2), (0, 3)}, {(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2)}, 10⟩
theorem entry_407_checked : entryAt 407 = entry_407 := by
  rw [entry_chunk_20 1 (by decide)]
  decide +kernel
theorem row_407 : rowAt 407 = data_407 := by
  rw [rowAt, dif_neg (by decide : ¬ 407 < 6), entry_407_checked]
  change forkRow [placeRow ⟨285, 0, 3, 7⟩ (rowAt 285), placeRow ⟨314, 6, 5, 4⟩ (rowAt 314)] = data_407
  rw [row_285, row_314]
  apply row_ext <;> decide +kernel
theorem entry_good_407 : EntryGood 407 := by
  unfold EntryGood
  rw [entry_407_checked]
  decide +kernel
theorem good_407 : Good (rowAt 407) := by
  rw [row_407]
  unfold Good
  decide +kernel

def data_408 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1), (1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (5, -1)}, 11⟩
theorem entry_408_checked : entryAt 408 = entry_408 := by
  rw [entry_chunk_20 2 (by decide)]
  decide +kernel
theorem row_408 : rowAt 408 = data_408 := by
  rw [rowAt, dif_neg (by decide : ¬ 408 < 6), entry_408_checked]
  change forkRow [placeRow ⟨357, 0, 5, 2⟩ (rowAt 357), placeRow ⟨229, 7, 2, 4⟩ (rowAt 229), placeRow ⟨223, 4, 2, 4⟩ (rowAt 223), placeRow ⟨223, 0, 6, 4⟩ (rowAt 223)] = data_408
  rw [row_357, row_229, row_223]
  apply row_ext <;> decide +kernel
theorem entry_good_408 : EntryGood 408 := by
  unfold EntryGood
  rw [entry_408_checked]
  decide +kernel
theorem good_408 : Good (rowAt 408) := by
  rw [row_408]
  unfold Good
  decide +kernel

def data_409 : RowData := ⟨{(0, -3), (0, -2), (1, -3), (2, -1), (2, 0)}, {(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 12⟩
theorem entry_409_checked : entryAt 409 = entry_409 := by
  rw [entry_chunk_20 3 (by decide)]
  decide +kernel
theorem row_409 : rowAt 409 = data_409 := by
  rw [rowAt, dif_neg (by decide : ¬ 409 < 6), entry_409_checked]
  change forkRow [placeRow ⟨136, 6, 4, 3⟩ (rowAt 136), placeRow ⟨384, 0, 5, 4⟩ (rowAt 384), placeRow ⟨133, 4, 4, 3⟩ (rowAt 133), placeRow ⟨110, 3, 4, 3⟩ (rowAt 110)] = data_409
  rw [row_136, row_384, row_133, row_110]
  apply row_ext <;> decide +kernel
theorem entry_good_409 : EntryGood 409 := by
  unfold EntryGood
  rw [entry_409_checked]
  decide +kernel
theorem good_409 : Good (rowAt 409) := by
  rw [row_409]
  unfold Good
  decide +kernel

def data_410 : RowData := ⟨{(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1)}, {(-6, 2), (-6, 4), (-5, 2), (-5, 3), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (4, 2)}, 14⟩
theorem entry_410_checked : entryAt 410 = entry_410 := by
  rw [entry_chunk_20 4 (by decide)]
  decide +kernel
theorem row_410 : rowAt 410 = data_410 := by
  rw [rowAt, dif_neg (by decide : ¬ 410 < 6), entry_410_checked]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (rowAt 0), placeRow ⟨405, 0, 3, 7⟩ (rowAt 405)] = data_410
  rw [row_0, row_405]
  apply row_ext <;> decide +kernel
theorem entry_good_410 : EntryGood 410 := by
  unfold EntryGood
  rw [entry_410_checked]
  decide +kernel
theorem good_410 : Good (rowAt 410) := by
  rw [row_410]
  unfold Good
  decide +kernel

def data_411 : RowData := ⟨{(1, 0), (2, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1), (7, 3)}, 14⟩
theorem entry_411_checked : entryAt 411 = entry_411 := by
  rw [entry_chunk_20 5 (by decide)]
  decide +kernel
theorem row_411 : rowAt 411 = data_411 := by
  rw [rowAt, dif_neg (by decide : ¬ 411 < 6), entry_411_checked]
  change forkRow [placeRow ⟨252, 0, 7, 4⟩ (rowAt 252), placeRow ⟨263, 0, 7, 4⟩ (rowAt 263), placeRow ⟨300, 3, 3, 4⟩ (rowAt 300), placeRow ⟨379, 1, 7, 4⟩ (rowAt 379), placeRow ⟨173, 0, 7, 4⟩ (rowAt 173), placeRow ⟨246, 0, 7, 4⟩ (rowAt 246)] = data_411
  rw [row_252, row_263, row_300, row_379, row_173, row_246]
  apply row_ext <;> decide +kernel
theorem entry_good_411 : EntryGood 411 := by
  unfold EntryGood
  rw [entry_411_checked]
  decide +kernel
theorem good_411 : Good (rowAt 411) := by
  rw [row_411]
  unfold Good
  decide +kernel

def data_412 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0), (-1, 1)}, {(-6, 1), (-5, 1), (-5, 2), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)}, 13⟩
theorem entry_412_checked : entryAt 412 = entry_412 := by
  rw [entry_chunk_20 6 (by decide)]
  decide +kernel
theorem row_412 : rowAt 412 = data_412 := by
  rw [rowAt, dif_neg (by decide : ¬ 412 < 6), entry_412_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨403, 4, 3, 6⟩ (rowAt 403)] = data_412
  rw [row_0, row_403]
  apply row_ext <;> decide +kernel
theorem entry_good_412 : EntryGood 412 := by
  unfold EntryGood
  rw [entry_412_checked]
  decide +kernel
theorem good_412 : Good (rowAt 412) := by
  rw [row_412]
  unfold Good
  decide +kernel

def data_413 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 1), (0, 1), (0, 2)}, {(-5, 2), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (5, 2)}, 13⟩
theorem entry_413_checked : entryAt 413 = entry_413 := by
  rw [entry_chunk_20 7 (by decide)]
  decide +kernel
theorem row_413 : rowAt 413 = data_413 := by
  rw [rowAt, dif_neg (by decide : ¬ 413 < 6), entry_413_checked]
  change forkRow [placeRow ⟨3, 7, 4, 3⟩ (rowAt 3), placeRow ⟨403, 0, 4, 7⟩ (rowAt 403)] = data_413
  rw [row_3, row_403]
  apply row_ext <;> decide +kernel
theorem entry_good_413 : EntryGood 413 := by
  unfold EntryGood
  rw [entry_413_checked]
  decide +kernel
theorem good_413 : Good (rowAt 413) := by
  rw [row_413]
  unfold Good
  decide +kernel

def data_414 : RowData := ⟨{(-1, -1), (-1, 1), (0, -1), (0, 1)}, {(-5, 0), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -2), (2, 0), (2, 1), (2, 2), (3, -2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)}, 11⟩
theorem entry_414_checked : entryAt 414 = entry_414 := by
  rw [entry_chunk_20 8 (by decide)]
  decide +kernel
theorem row_414 : rowAt 414 = data_414 := by
  rw [rowAt, dif_neg (by decide : ¬ 414 < 6), entry_414_checked]
  change forkRow [placeRow ⟨374, 0, 2, 5⟩ (rowAt 374), placeRow ⟨199, 2, 4, 2⟩ (rowAt 199), placeRow ⟨185, 2, 4, 2⟩ (rowAt 185)] = data_414
  rw [row_374, row_199, row_185]
  apply row_ext <;> decide +kernel
theorem entry_good_414 : EntryGood 414 := by
  unfold EntryGood
  rw [entry_414_checked]
  decide +kernel
theorem good_414 : Good (rowAt 414) := by
  rw [row_414]
  unfold Good
  decide +kernel

def data_415 : RowData := ⟨{(-3, -3), (-2, -3), (-2, 0), (-1, -3), (0, -3)}, {(-5, 1), (-4, 0), (-4, 1), (-3, -3), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 12⟩
theorem entry_415_checked : entryAt 415 = entry_415 := by
  rw [entry_chunk_20 9 (by decide)]
  decide +kernel
theorem row_415 : rowAt 415 = data_415 := by
  rw [rowAt, dif_neg (by decide : ¬ 415 < 6), entry_415_checked]
  change forkRow [placeRow ⟨177, 1, 4, 2⟩ (rowAt 177), placeRow ⟨164, 1, 4, 2⟩ (rowAt 164), placeRow ⟨205, 1, 5, 2⟩ (rowAt 205), placeRow ⟨384, 0, 3, 4⟩ (rowAt 384), placeRow ⟨371, 0, 5, 4⟩ (rowAt 371)] = data_415
  rw [row_177, row_164, row_205, row_384, row_371]
  apply row_ext <;> decide +kernel
theorem entry_good_415 : EntryGood 415 := by
  unfold EntryGood
  rw [entry_415_checked]
  decide +kernel
theorem good_415 : Good (rowAt 415) := by
  rw [row_415]
  unfold Good
  decide +kernel

#check row_415
def data_416 : RowData := ⟨{(-2, 0), (-1, 0)}, {(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, 1)}, 16⟩
theorem entry_416_checked : entryAt 416 = entry_416 := by
  rw [entry_chunk_20 10 (by decide)]
  decide +kernel
theorem row_416 : rowAt 416 = data_416 := by
  rw [rowAt, dif_neg (by decide : ¬ 416 < 6), entry_416_checked]
  change forkRow [placeRow ⟨176, 2, 5, 4⟩ (rowAt 176), placeRow ⟨385, 4, 1, 4⟩ (rowAt 385), placeRow ⟨197, 4, 1, 4⟩ (rowAt 197), placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨245, 2, 5, 4⟩ (rowAt 245), placeRow ⟨220, 2, 5, 4⟩ (rowAt 220)] = data_416
  rw [row_176, row_385, row_197, row_295, row_245, row_220]
  apply row_ext <;> decide +kernel
theorem entry_good_416 : EntryGood 416 := by
  unfold EntryGood
  rw [entry_416_checked]
  decide +kernel
theorem good_416 : Good (rowAt 416) := by
  rw [row_416]
  unfold Good
  decide +kernel

def data_417 : RowData := ⟨{(-2, -3), (-2, -2), (-1, -3), (0, -3), (0, -1), (1, -3)}, {(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 13⟩
theorem entry_417_checked : entryAt 417 = entry_417 := by
  rw [entry_chunk_20 11 (by decide)]
  decide +kernel
theorem row_417 : rowAt 417 = data_417 := by
  rw [rowAt, dif_neg (by decide : ¬ 417 < 6), entry_417_checked]
  change forkRow [placeRow ⟨409, 0, 2, 4⟩ (rowAt 409), placeRow ⟨11, 1, 4, 2⟩ (rowAt 11), placeRow ⟨270, 4, 4, 2⟩ (rowAt 270)] = data_417
  rw [row_409, row_11, row_270]
  apply row_ext <;> decide +kernel
theorem entry_good_417 : EntryGood 417 := by
  unfold EntryGood
  rw [entry_417_checked]
  decide +kernel
theorem good_417 : Good (rowAt 417) := by
  rw [row_417]
  unfold Good
  decide +kernel

def data_418 : RowData := ⟨{(-2, -1), (-1, -4), (-1, -3), (-1, -1), (0, -1)}, {(-5, 0), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)}, 14⟩
theorem entry_418_checked : entryAt 418 = entry_418 := by
  rw [entry_chunk_20 12 (by decide)]
  decide +kernel
theorem row_418 : rowAt 418 = data_418 := by
  rw [rowAt, dif_neg (by decide : ¬ 418 < 6), entry_418_checked]
  change forkRow [placeRow ⟨68, 4, 1, 3⟩ (rowAt 68), placeRow ⟨62, 6, 1, 3⟩ (rowAt 62), placeRow ⟨147, 6, 1, 3⟩ (rowAt 147), placeRow ⟨413, 0, 4, 2⟩ (rowAt 413)] = data_418
  rw [row_68, row_62, row_147, row_413]
  apply row_ext <;> decide +kernel
theorem entry_good_418 : EntryGood 418 := by
  unfold EntryGood
  rw [entry_418_checked]
  decide +kernel
theorem good_418 : Good (rowAt 418) := by
  rw [row_418]
  unfold Good
  decide +kernel

def data_419 : RowData := ⟨{(-3, -3), (-2, -3), (-2, -2), (-1, -3), (0, -3)}, {(-5, 1), (-4, -4), (-4, 0), (-4, 1), (-3, -4), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 13⟩
theorem entry_419_checked : entryAt 419 = entry_419 := by
  rw [entry_chunk_20 13 (by decide)]
  decide +kernel
theorem row_419 : rowAt 419 = data_419 := by
  rw [rowAt, dif_neg (by decide : ¬ 419 < 6), entry_419_checked]
  change forkRow [placeRow ⟨243, 0, 4, 2⟩ (rowAt 243), placeRow ⟨164, 1, 4, 2⟩ (rowAt 164), placeRow ⟨402, 0, 2, 4⟩ (rowAt 402), placeRow ⟨253, 0, 2, 4⟩ (rowAt 253), placeRow ⟨377, 0, 2, 4⟩ (rowAt 377)] = data_419
  rw [row_243, row_164, row_402, row_253, row_377]
  apply row_ext <;> decide +kernel
theorem entry_good_419 : EntryGood 419 := by
  unfold EntryGood
  rw [entry_419_checked]
  decide +kernel
theorem good_419 : Good (rowAt 419) := by
  rw [row_419]
  unfold Good
  decide +kernel

def data_420 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3)}, {(-3, 1), (-2, -4), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 13⟩
theorem entry_420_checked : entryAt 420 = entry_420 := by
  rw [entry_chunk_20 14 (by decide)]
  decide +kernel
theorem row_420 : rowAt 420 = data_420 := by
  rw [rowAt, dif_neg (by decide : ¬ 420 < 6), entry_420_checked]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (rowAt 29), placeRow ⟨415, 0, 6, 4⟩ (rowAt 415)] = data_420
  rw [row_29, row_415]
  apply row_ext <;> decide +kernel
theorem entry_good_420 : EntryGood 420 := by
  unfold EntryGood
  rw [entry_420_checked]
  decide +kernel
theorem good_420 : Good (rowAt 420) := by
  rw [row_420]
  unfold Good
  decide +kernel

def data_421 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0), (1, 0)}, {(-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (3, -3), (3, -2), (3, -1), (4, -3), (4, -2), (4, -1), (5, -3), (5, -1)}, 12⟩
theorem entry_421_checked : entryAt 421 = entry_421 := by
  rw [entry_chunk_20 15 (by decide)]
  decide +kernel
theorem row_421 : rowAt 421 = data_421 := by
  rw [rowAt, dif_neg (by decide : ¬ 421 < 6), entry_421_checked]
  change forkRow [placeRow ⟨24, 6, 2, 3⟩ (rowAt 24), placeRow ⟨397, 1, 5, 3⟩ (rowAt 397), placeRow ⟨25, 6, 2, 3⟩ (rowAt 25), placeRow ⟨241, 4, 2, 4⟩ (rowAt 241)] = data_421
  rw [row_24, row_397, row_25, row_241]
  apply row_ext <;> decide +kernel
theorem entry_good_421 : EntryGood 421 := by
  unfold EntryGood
  rw [entry_421_checked]
  decide +kernel
theorem good_421 : Good (rowAt 421) := by
  rw [row_421]
  unfold Good
  decide +kernel

def data_422 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (-1, 2)}, {(-4, -1), (-3, -1), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)}, 14⟩
theorem entry_422_checked : entryAt 422 = entry_422 := by
  rw [entry_chunk_20 16 (by decide)]
  decide +kernel
theorem row_422 : rowAt 422 = data_422 := by
  rw [rowAt, dif_neg (by decide : ¬ 422 < 6), entry_422_checked]
  change forkRow [placeRow ⟨45, 1, 3, 7⟩ (rowAt 45), placeRow ⟨106, 6, 2, 3⟩ (rowAt 106), placeRow ⟨419, 1, 6, 6⟩ (rowAt 419)] = data_422
  rw [row_45, row_106, row_419]
  apply row_ext <;> decide +kernel
theorem entry_good_422 : EntryGood 422 := by
  unfold EntryGood
  rw [entry_422_checked]
  decide +kernel
theorem good_422 : Good (rowAt 422) := by
  rw [row_422]
  unfold Good
  decide +kernel

def data_423 : RowData := ⟨{(-1, -2), (-1, 0), (0, -2)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1)}, 12⟩
theorem entry_423_checked : entryAt 423 = entry_423 := by
  rw [entry_chunk_20 17 (by decide)]
  decide +kernel
theorem row_423 : rowAt 423 = data_423 := by
  rw [rowAt, dif_neg (by decide : ¬ 423 < 6), entry_423_checked]
  change forkRow [placeRow ⟨378, 4, 2, 4⟩ (rowAt 378), placeRow ⟨386, 0, 5, 4⟩ (rowAt 386), placeRow ⟨226, 3, 3, 5⟩ (rowAt 226), placeRow ⟨386, 4, 2, 4⟩ (rowAt 386), placeRow ⟨378, 0, 5, 4⟩ (rowAt 378)] = data_423
  rw [row_378, row_386, row_226]
  apply row_ext <;> decide +kernel
theorem entry_good_423 : EntryGood 423 := by
  unfold EntryGood
  rw [entry_423_checked]
  decide +kernel
theorem good_423 : Good (rowAt 423) := by
  rw [row_423]
  unfold Good
  decide +kernel

def data_424 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (2, -1)}, {(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (6, 1), (7, -2), (7, -1), (7, 0), (7, 1)}, 10⟩
theorem entry_424_checked : entryAt 424 = entry_424 := by
  rw [entry_chunk_20 18 (by decide)]
  decide +kernel
theorem row_424 : rowAt 424 = data_424 := by
  rw [rowAt, dif_neg (by decide : ¬ 424 < 6), entry_424_checked]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (rowAt 55), placeRow ⟨394, 0, 6, 4⟩ (rowAt 394), placeRow ⟨216, 3, 4, 5⟩ (rowAt 216)] = data_424
  rw [row_55, row_394, row_216]
  apply row_ext <;> decide +kernel
theorem entry_good_424 : EntryGood 424 := by
  unfold EntryGood
  rw [entry_424_checked]
  decide +kernel
theorem good_424 : Good (rowAt 424) := by
  rw [row_424]
  unfold Good
  decide +kernel

def data_425 : RowData := ⟨{(-1, -2), (-1, 0), (0, -2)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1)}, 12⟩
theorem entry_425_checked : entryAt 425 = entry_425 := by
  rw [entry_chunk_20 19 (by decide)]
  decide +kernel
theorem row_425 : rowAt 425 = data_425 := by
  rw [rowAt, dif_neg (by decide : ¬ 425 < 6), entry_425_checked]
  change forkRow [placeRow ⟨386, 0, 5, 4⟩ (rowAt 386), placeRow ⟨226, 1, 4, 5⟩ (rowAt 226), placeRow ⟨378, 4, 2, 4⟩ (rowAt 378), placeRow ⟨378, 0, 5, 4⟩ (rowAt 378), placeRow ⟨386, 4, 2, 4⟩ (rowAt 386)] = data_425
  rw [row_386, row_226, row_378]
  apply row_ext <;> decide +kernel
theorem entry_good_425 : EntryGood 425 := by
  unfold EntryGood
  rw [entry_425_checked]
  decide +kernel
theorem good_425 : Good (rowAt 425) := by
  rw [row_425]
  unfold Good
  decide +kernel

def data_426 : RowData := ⟨{(-1, -2), (0, -2), (0, -1)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0)}, 12⟩
theorem entry_426_checked : entryAt 426 = entry_426 := by
  rw [entry_chunk_21 0 (by decide)]
  decide +kernel
theorem row_426 : rowAt 426 = data_426 := by
  rw [rowAt, dif_neg (by decide : ¬ 426 < 6), entry_426_checked]
  change forkRow [placeRow ⟨300, 6, 4, 1⟩ (rowAt 300), placeRow ⟨252, 1, 4, 5⟩ (rowAt 252), placeRow ⟨397, 0, 3, 4⟩ (rowAt 397), placeRow ⟨291, 1, 4, 1⟩ (rowAt 291), placeRow ⟨328, 0, 4, 5⟩ (rowAt 328), placeRow ⟨319, 1, 3, 5⟩ (rowAt 319)] = data_426
  rw [row_300, row_252, row_397, row_291, row_328, row_319]
  apply row_ext <;> decide +kernel
theorem entry_good_426 : EntryGood 426 := by
  unfold EntryGood
  rw [entry_426_checked]
  decide +kernel
theorem good_426 : Good (rowAt 426) := by
  rw [row_426]
  unfold Good
  decide +kernel

def data_427 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (-1, 2)}, {(-4, -1), (-3, -1), (-2, -2), (-2, -1), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)}, 14⟩
theorem entry_427_checked : entryAt 427 = entry_427 := by
  rw [entry_chunk_21 1 (by decide)]
  decide +kernel
theorem row_427 : rowAt 427 = data_427 := by
  rw [rowAt, dif_neg (by decide : ¬ 427 < 6), entry_427_checked]
  change forkRow [placeRow ⟨45, 1, 3, 7⟩ (rowAt 45), placeRow ⟨106, 6, 2, 3⟩ (rowAt 106), placeRow ⟨420, 1, 6, 4⟩ (rowAt 420)] = data_427
  rw [row_45, row_106, row_420]
  apply row_ext <;> decide +kernel
theorem entry_good_427 : EntryGood 427 := by
  unfold EntryGood
  rw [entry_427_checked]
  decide +kernel
theorem good_427 : Good (rowAt 427) := by
  rw [row_427]
  unfold Good
  decide +kernel

def data_428 : RowData := ⟨{(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2)}, {(-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 17⟩
theorem entry_428_checked : entryAt 428 = entry_428 := by
  rw [entry_chunk_21 2 (by decide)]
  decide +kernel
theorem row_428 : rowAt 428 = data_428 := by
  rw [rowAt, dif_neg (by decide : ¬ 428 < 6), entry_428_checked]
  change forkRow [placeRow ⟨26, 3, 4, 3⟩ (rowAt 26), placeRow ⟨416, 0, 5, 4⟩ (rowAt 416), placeRow ⟨244, 0, 5, 4⟩ (rowAt 244), placeRow ⟨329, 0, 4, 3⟩ (rowAt 329)] = data_428
  rw [row_26, row_416, row_244, row_329]
  apply row_ext <;> decide +kernel
theorem entry_good_428 : EntryGood 428 := by
  unfold EntryGood
  rw [entry_428_checked]
  decide +kernel
theorem good_428 : Good (rowAt 428) := by
  rw [row_428]
  unfold Good
  decide +kernel

def data_429 : RowData := ⟨{(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)}, {(-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1)}, 6⟩
theorem entry_429_checked : entryAt 429 = entry_429 := by
  rw [entry_chunk_21 3 (by decide)]
  decide +kernel
theorem row_429 : rowAt 429 = data_429 := by
  rw [rowAt, dif_neg (by decide : ¬ 429 < 6), entry_429_checked]
  change forkRow [placeRow ⟨128, 0, 6, 3⟩ (rowAt 128), placeRow ⟨28, 3, 4, 5⟩ (rowAt 28)] = data_429
  rw [row_128, row_28]
  apply row_ext <;> decide +kernel
theorem entry_good_429 : EntryGood 429 := by
  unfold EntryGood
  rw [entry_429_checked]
  decide +kernel
theorem good_429 : Good (rowAt 429) := by
  rw [row_429]
  unfold Good
  decide +kernel

def data_430 : RowData := ⟨{(-2, -2), (-2, -1), (-2, 0), (-1, -2), (0, -2)}, {(-7, -1), (-7, 1), (-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -1), (2, 0), (2, 1), (3, -3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 10⟩
theorem entry_430_checked : entryAt 430 = entry_430 := by
  rw [entry_chunk_21 4 (by decide)]
  decide +kernel
theorem row_430 : rowAt 430 = data_430 := by
  rw [rowAt, dif_neg (by decide : ¬ 430 < 6), entry_430_checked]
  change forkRow [placeRow ⟨277, 7, 1, 3⟩ (rowAt 277), placeRow ⟨338, 4, 3, 4⟩ (rowAt 338), placeRow ⟨336, 1, 4, 3⟩ (rowAt 336), placeRow ⟨375, 2, 4, 3⟩ (rowAt 375), placeRow ⟨277, 6, 3, 1⟩ (rowAt 277)] = data_430
  rw [row_277, row_338, row_336, row_375]
  apply row_ext <;> decide +kernel
theorem entry_good_430 : EntryGood 430 := by
  unfold EntryGood
  rw [entry_430_checked]
  decide +kernel
theorem good_430 : Good (rowAt 430) := by
  rw [row_430]
  unfold Good
  decide +kernel

def data_431 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (0, -3), (1, -3), (2, -3)}, {(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (6, 1)}, 13⟩
theorem entry_431_checked : entryAt 431 = entry_431 := by
  rw [entry_chunk_21 5 (by decide)]
  decide +kernel
theorem row_431 : rowAt 431 = data_431 := by
  rw [rowAt, dif_neg (by decide : ¬ 431 < 6), entry_431_checked]
  change forkRow [placeRow ⟨73, 4, 3, 3⟩ (rowAt 73), placeRow ⟨302, 1, 5, 2⟩ (rowAt 302), placeRow ⟨415, 0, 6, 4⟩ (rowAt 415), placeRow ⟨398, 0, 6, 4⟩ (rowAt 398)] = data_431
  rw [row_73, row_302, row_415, row_398]
  apply row_ext <;> decide +kernel
theorem entry_good_431 : EntryGood 431 := by
  unfold EntryGood
  rw [entry_431_checked]
  decide +kernel
theorem good_431 : Good (rowAt 431) := by
  rw [row_431]
  unfold Good
  decide +kernel

def data_432 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (1, -3), (1, -2)}, {(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 1)}, 18⟩
theorem entry_432_checked : entryAt 432 = entry_432 := by
  rw [entry_chunk_21 6 (by decide)]
  decide +kernel
theorem row_432 : rowAt 432 = data_432 := by
  rw [rowAt, dif_neg (by decide : ¬ 432 < 6), entry_432_checked]
  change forkRow [placeRow ⟨42, 3, 4, 3⟩ (rowAt 42), placeRow ⟨428, 0, 5, 4⟩ (rowAt 428), placeRow ⟨274, 0, 4, 3⟩ (rowAt 274)] = data_432
  rw [row_42, row_428, row_274]
  apply row_ext <;> decide +kernel
theorem entry_good_432 : EntryGood 432 := by
  unfold EntryGood
  rw [entry_432_checked]
  decide +kernel
theorem good_432 : Good (rowAt 432) := by
  rw [row_432]
  unfold Good
  decide +kernel

def data_433 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1)}, {(-3, -3), (-2, -3), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -1), (7, 0), (7, 1), (7, 2)}, 15⟩
theorem entry_433_checked : entryAt 433 = entry_433 := by
  rw [entry_chunk_21 7 (by decide)]
  decide +kernel
theorem row_433 : rowAt 433 = data_433 := by
  rw [rowAt, dif_neg (by decide : ¬ 433 < 6), entry_433_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨427, 0, 5, 2⟩ (rowAt 427), placeRow ⟨422, 0, 5, 2⟩ (rowAt 422)] = data_433
  rw [row_63, row_7, row_427, row_422]
  apply row_ext <;> decide +kernel
theorem entry_good_433 : EntryGood 433 := by
  unfold EntryGood
  rw [entry_433_checked]
  decide +kernel
theorem good_433 : Good (rowAt 433) := by
  rw [row_433]
  unfold Good
  decide +kernel

def data_434 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, 0), (0, -2)}, {(-5, 1), (-5, 3), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1)}, 15⟩
theorem entry_434_checked : entryAt 434 = entry_434 := by
  rw [entry_chunk_21 8 (by decide)]
  decide +kernel
theorem row_434 : rowAt 434 = data_434 := by
  rw [rowAt, dif_neg (by decide : ¬ 434 < 6), entry_434_checked]
  change forkRow [placeRow ⟨418, 0, 4, 5⟩ (rowAt 418), placeRow ⟨263, 2, 5, 4⟩ (rowAt 263), placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨176, 2, 5, 4⟩ (rowAt 176), placeRow ⟨116, 0, 4, 3⟩ (rowAt 116)] = data_434
  rw [row_418, row_263, row_295, row_176, row_116]
  apply row_ext <;> decide +kernel
theorem entry_good_434 : EntryGood 434 := by
  unfold EntryGood
  rw [entry_434_checked]
  decide +kernel
theorem good_434 : Good (rowAt 434) := by
  rw [row_434]
  unfold Good
  decide +kernel

def data_435 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (2, -1), (3, -1)}, {(-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2), (7, 3)}, 14⟩
theorem entry_435_checked : entryAt 435 = entry_435 := by
  rw [entry_chunk_21 9 (by decide)]
  decide +kernel
theorem row_435 : rowAt 435 = data_435 := by
  rw [rowAt, dif_neg (by decide : ¬ 435 < 6), entry_435_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨431, 0, 5, 6⟩ (rowAt 431)] = data_435
  rw [row_6, row_431]
  apply row_ext <;> decide +kernel
theorem entry_good_435 : EntryGood 435 := by
  unfold EntryGood
  rw [entry_435_checked]
  decide +kernel
theorem good_435 : Good (rowAt 435) := by
  rw [row_435]
  unfold Good
  decide +kernel

def data_436 : RowData := ⟨{(0, -3), (0, -2), (1, -3), (1, -2)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 1)}, 18⟩
theorem entry_436_checked : entryAt 436 = entry_436 := by
  rw [entry_chunk_21 10 (by decide)]
  decide +kernel
theorem row_436 : rowAt 436 = data_436 := by
  rw [rowAt, dif_neg (by decide : ¬ 436 < 6), entry_436_checked]
  change forkRow [placeRow ⟨51, 1, 5, 4⟩ (rowAt 51), placeRow ⟨60, 3, 4, 3⟩ (rowAt 60), placeRow ⟨274, 4, 4, 3⟩ (rowAt 274), placeRow ⟨428, 0, 5, 4⟩ (rowAt 428)] = data_436
  rw [row_51, row_60, row_274, row_428]
  apply row_ext <;> decide +kernel
theorem entry_good_436 : EntryGood 436 := by
  unfold EntryGood
  rw [entry_436_checked]
  decide +kernel
theorem good_436 : Good (rowAt 436) := by
  rw [row_436]
  unfold Good
  decide +kernel

def data_437 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-3, -3), (-2, -3), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -1), (7, 0), (7, 1), (7, 2)}, 15⟩
theorem entry_437_checked : entryAt 437 = entry_437 := by
  rw [entry_chunk_21 11 (by decide)]
  decide +kernel
theorem row_437 : rowAt 437 = data_437 := by
  rw [rowAt, dif_neg (by decide : ¬ 437 < 6), entry_437_checked]
  change forkRow [placeRow ⟨55, 7, 4, 0⟩ (rowAt 55), placeRow ⟨427, 0, 5, 2⟩ (rowAt 427), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨422, 0, 5, 2⟩ (rowAt 422)] = data_437
  rw [row_55, row_427, row_63, row_422]
  apply row_ext <;> decide +kernel
theorem entry_good_437 : EntryGood 437 := by
  unfold EntryGood
  rw [entry_437_checked]
  decide +kernel
theorem good_437 : Good (rowAt 437) := by
  rw [row_437]
  unfold Good
  decide +kernel

def data_438 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, -1), (1, 0)}, {(-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)}, 19⟩
theorem entry_438_checked : entryAt 438 = entry_438 := by
  rw [entry_chunk_21 12 (by decide)]
  decide +kernel
theorem row_438 : rowAt 438 = data_438 := by
  rw [rowAt, dif_neg (by decide : ¬ 438 < 6), entry_438_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨432, 0, 4, 6⟩ (rowAt 432)] = data_438
  rw [row_0, row_432]
  apply row_ext <;> decide +kernel
theorem entry_good_438 : EntryGood 438 := by
  unfold EntryGood
  rw [entry_438_checked]
  decide +kernel
theorem good_438 : Good (rowAt 438) := by
  rw [row_438]
  unfold Good
  decide +kernel

def data_439 : RowData := ⟨{(-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, 0)}, {(-5, 1), (-5, 3), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1)}, 15⟩
theorem entry_439_checked : entryAt 439 = entry_439 := by
  rw [entry_chunk_21 13 (by decide)]
  decide +kernel
theorem row_439 : rowAt 439 = data_439 := by
  rw [rowAt, dif_neg (by decide : ¬ 439 < 6), entry_439_checked]
  change forkRow [placeRow ⟨176, 2, 5, 4⟩ (rowAt 176), placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨263, 2, 5, 4⟩ (rowAt 263), placeRow ⟨418, 0, 4, 5⟩ (rowAt 418), placeRow ⟨149, 0, 4, 3⟩ (rowAt 149)] = data_439
  rw [row_176, row_295, row_263, row_418, row_149]
  apply row_ext <;> decide +kernel
theorem entry_good_439 : EntryGood 439 := by
  unfold EntryGood
  rw [entry_439_checked]
  decide +kernel
theorem good_439 : Good (rowAt 439) := by
  rw [row_439]
  unfold Good
  decide +kernel

def data_440 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0), (1, 0)}, {(-4, 4), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4)}, 15⟩
theorem entry_440_checked : entryAt 440 = entry_440 := by
  rw [entry_chunk_21 14 (by decide)]
  decide +kernel
theorem row_440 : rowAt 440 = data_440 := by
  rw [rowAt, dif_neg (by decide : ¬ 440 < 6), entry_440_checked]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (rowAt 6), placeRow ⟨435, 0, 2, 5⟩ (rowAt 435)] = data_440
  rw [row_6, row_435]
  apply row_ext <;> decide +kernel
theorem entry_good_440 : EntryGood 440 := by
  unfold EntryGood
  rw [entry_440_checked]
  decide +kernel
theorem good_440 : Good (rowAt 440) := by
  rw [row_440]
  unfold Good
  decide +kernel

def data_441 : RowData := ⟨{(0, 1), (1, 1), (2, 1), (3, 1)}, {(-2, 5), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 4), (7, 5)}, 15⟩
theorem entry_441_checked : entryAt 441 = entry_441 := by
  rw [entry_chunk_21 15 (by decide)]
  decide +kernel
theorem row_441 : rowAt 441 = data_441 := by
  rw [rowAt, dif_neg (by decide : ¬ 441 < 6), entry_441_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨435, 0, 4, 6⟩ (rowAt 435)] = data_441
  rw [row_6, row_435]
  apply row_ext <;> decide +kernel
theorem entry_good_441 : EntryGood 441 := by
  unfold EntryGood
  rw [entry_441_checked]
  decide +kernel
theorem good_441 : Good (rowAt 441) := by
  rw [row_441]
  unfold Good
  decide +kernel

def data_442 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1)}, {(-3, -2), (-2, -2), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2), (7, 3)}, 16⟩
theorem entry_442_checked : entryAt 442 = entry_442 := by
  rw [entry_chunk_21 16 (by decide)]
  decide +kernel
theorem row_442 : rowAt 442 = data_442 := by
  rw [rowAt, dif_neg (by decide : ¬ 442 < 6), entry_442_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨7, 1, 5, 4⟩ (rowAt 7), placeRow ⟨433, 0, 4, 5⟩ (rowAt 433), placeRow ⟨201, 0, 3, 2⟩ (rowAt 201)] = data_442
  rw [row_63, row_7, row_433, row_201]
  apply row_ext <;> decide +kernel
theorem entry_good_442 : EntryGood 442 := by
  unfold EntryGood
  rw [entry_442_checked]
  decide +kernel
theorem good_442 : Good (rowAt 442) := by
  rw [row_442]
  unfold Good
  decide +kernel

def data_443 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (0, -1)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)}, 20⟩
theorem entry_443_checked : entryAt 443 = entry_443 := by
  rw [entry_chunk_21 17 (by decide)]
  decide +kernel
theorem row_443 : rowAt 443 = data_443 := by
  rw [rowAt, dif_neg (by decide : ¬ 443 < 6), entry_443_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨438, 0, 3, 4⟩ (rowAt 438)] = data_443
  rw [row_6, row_438]
  apply row_ext <;> decide +kernel
theorem entry_good_443 : EntryGood 443 := by
  unfold EntryGood
  rw [entry_443_checked]
  decide +kernel
theorem good_443 : Good (rowAt 443) := by
  rw [row_443]
  unfold Good
  decide +kernel

def data_444 : RowData := ⟨{(-2, -2), (-1, -2), (0, -2), (0, -1)}, {(-5, -3), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)}, 14⟩
theorem entry_444_checked : entryAt 444 = entry_444 := by
  rw [entry_chunk_21 18 (by decide)]
  decide +kernel
theorem row_444 : rowAt 444 = data_444 := by
  rw [rowAt, dif_neg (by decide : ¬ 444 < 6), entry_444_checked]
  change forkRow [placeRow ⟨194, 0, 5, 3⟩ (rowAt 194), placeRow ⟨160, 3, 4, 1⟩ (rowAt 160), placeRow ⟨142, 7, 4, 1⟩ (rowAt 142), placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨353, 4, 1, 2⟩ (rowAt 353), placeRow ⟨412, 0, 5, 3⟩ (rowAt 412)] = data_444
  rw [row_194, row_160, row_142, row_236, row_353, row_412]
  apply row_ext <;> decide +kernel
theorem entry_good_444 : EntryGood 444 := by
  unfold EntryGood
  rw [entry_444_checked]
  decide +kernel
theorem good_444 : Good (rowAt 444) := by
  rw [row_444]
  unfold Good
  decide +kernel

def data_445 : RowData := ⟨{(1, 0), (1, 1), (2, 0), (2, 1)}, {(-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (7, 2), (7, 4)}, 19⟩
theorem entry_445_checked : entryAt 445 = entry_445 := by
  rw [entry_chunk_21 19 (by decide)]
  decide +kernel
theorem row_445 : rowAt 445 = data_445 := by
  rw [rowAt, dif_neg (by decide : ¬ 445 < 6), entry_445_checked]
  change forkRow [placeRow ⟨9, 4, 3, 4⟩ (rowAt 9), placeRow ⟨432, 0, 5, 7⟩ (rowAt 432)] = data_445
  rw [row_9, row_432]
  apply row_ext <;> decide +kernel
theorem entry_good_445 : EntryGood 445 := by
  unfold EntryGood
  rw [entry_445_checked]
  decide +kernel
theorem good_445 : Good (rowAt 445) := by
  rw [row_445]
  unfold Good
  decide +kernel

def data_446 : RowData := ⟨{(-1, -1), (1, 0), (2, 0), (3, 0), (3, 1)}, {(-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)}, 20⟩
theorem entry_446_checked : entryAt 446 = entry_446 := by
  rw [entry_chunk_22 0 (by decide)]
  decide +kernel
theorem row_446 : rowAt 446 = data_446 := by
  rw [rowAt, dif_neg (by decide : ¬ 446 < 6), entry_446_checked]
  change forkRow [placeRow ⟨4, 6, 4, 3⟩ (rowAt 4), placeRow ⟨438, 0, 6, 5⟩ (rowAt 438)] = data_446
  rw [row_4, row_438]
  apply row_ext <;> decide +kernel
theorem entry_good_446 : EntryGood 446 := by
  unfold EntryGood
  rw [entry_446_checked]
  decide +kernel
theorem good_446 : Good (rowAt 446) := by
  rw [row_446]
  unfold Good
  decide +kernel

def data_447 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1)}, {(-6, 1), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)}, 19⟩
theorem entry_447_checked : entryAt 447 = entry_447 := by
  rw [entry_chunk_22 1 (by decide)]
  decide +kernel
theorem row_447 : rowAt 447 = data_447 := by
  rw [rowAt, dif_neg (by decide : ¬ 447 < 6), entry_447_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨436, 4, 4, 6⟩ (rowAt 436)] = data_447
  rw [row_0, row_436]
  apply row_ext <;> decide +kernel
theorem entry_good_447 : EntryGood 447 := by
  unfold EntryGood
  rw [entry_447_checked]
  decide +kernel
theorem good_447 : Good (rowAt 447) := by
  rw [row_447]
  unfold Good
  decide +kernel

#check row_447
def data_448 : RowData := ⟨{(-2, -1), (-1, -1), (-1, 0), (0, -1)}, {(-5, 1), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)}, 19⟩
theorem entry_448_checked : entryAt 448 = entry_448 := by
  rw [entry_chunk_22 2 (by decide)]
  decide +kernel
theorem row_448 : rowAt 448 = data_448 := by
  rw [rowAt, dif_neg (by decide : ¬ 448 < 6), entry_448_checked]
  change forkRow [placeRow ⟨9, 4, 1, 3⟩ (rowAt 9), placeRow ⟨436, 0, 3, 6⟩ (rowAt 436)] = data_448
  rw [row_9, row_436]
  apply row_ext <;> decide +kernel
theorem entry_good_448 : EntryGood 448 := by
  unfold EntryGood
  rw [entry_448_checked]
  decide +kernel
theorem good_448 : Good (rowAt 448) := by
  rw [row_448]
  unfold Good
  decide +kernel

def data_449 : RowData := ⟨{(-1, -3), (-1, -2), (-1, 0), (0, -4), (0, -3), (0, -2)}, {(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1)}, 16⟩
theorem entry_449_checked : entryAt 449 = entry_449 := by
  rw [entry_chunk_22 3 (by decide)]
  decide +kernel
theorem row_449 : rowAt 449 = data_449 := by
  rw [rowAt, dif_neg (by decide : ¬ 449 < 6), entry_449_checked]
  change forkRow [placeRow ⟨26, 3, 4, 3⟩ (rowAt 26), placeRow ⟨244, 0, 5, 4⟩ (rowAt 244), placeRow ⟨439, 0, 5, 4⟩ (rowAt 439), placeRow ⟨307, 0, 4, 3⟩ (rowAt 307)] = data_449
  rw [row_26, row_244, row_439, row_307]
  apply row_ext <;> decide +kernel
theorem entry_good_449 : EntryGood 449 := by
  unfold EntryGood
  rw [entry_449_checked]
  decide +kernel
theorem good_449 : Good (rowAt 449) := by
  rw [row_449]
  unfold Good
  decide +kernel

def data_450 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, 0), (3, 0)}, {(-2, 4), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)}, 16⟩
theorem entry_450_checked : entryAt 450 = entry_450 := by
  rw [entry_chunk_22 4 (by decide)]
  decide +kernel
theorem row_450 : rowAt 450 = data_450 := by
  rw [rowAt, dif_neg (by decide : ¬ 450 < 6), entry_450_checked]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (rowAt 6), placeRow ⟨440, 0, 6, 4⟩ (rowAt 440)] = data_450
  rw [row_6, row_440]
  apply row_ext <;> decide +kernel
theorem entry_good_450 : EntryGood 450 := by
  unfold EntryGood
  rw [entry_450_checked]
  decide +kernel
theorem good_450 : Good (rowAt 450) := by
  rw [row_450]
  unfold Good
  decide +kernel

def data_451 : RowData := ⟨{(0, -3), (0, -2), (1, -4), (1, -3), (1, -2)}, {(-3, 1), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1)}, 17⟩
theorem entry_451_checked : entryAt 451 = entry_451 := by
  rw [entry_chunk_22 5 (by decide)]
  decide +kernel
theorem row_451 : rowAt 451 = data_451 := by
  rw [rowAt, dif_neg (by decide : ¬ 451 < 6), entry_451_checked]
  change forkRow [placeRow ⟨1, 5, 4, 3⟩ (rowAt 1), placeRow ⟨449, 0, 5, 4⟩ (rowAt 449)] = data_451
  rw [row_1, row_449]
  apply row_ext <;> decide +kernel
theorem entry_good_451 : EntryGood 451 := by
  unfold EntryGood
  rw [entry_451_checked]
  decide +kernel
theorem good_451 : Good (rowAt 451) := by
  rw [row_451]
  unfold Good
  decide +kernel

def data_452 : RowData := ⟨{(-1, 1), (-1, 2), (0, 1), (0, 2), (1, 2)}, {(-4, 5), (-4, 7), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5)}, 18⟩
theorem entry_452_checked : entryAt 452 = entry_452 := by
  rw [entry_chunk_22 6 (by decide)]
  decide +kernel
theorem row_452 : rowAt 452 = data_452 := by
  rw [rowAt, dif_neg (by decide : ¬ 452 < 6), entry_452_checked]
  change forkRow [placeRow ⟨24, 1, 5, 7⟩ (rowAt 24), placeRow ⟨451, 0, 3, 8⟩ (rowAt 451), placeRow ⟨25, 3, 3, 7⟩ (rowAt 25)] = data_452
  rw [row_24, row_451, row_25]
  apply row_ext <;> decide +kernel
theorem entry_good_452 : EntryGood 452 := by
  unfold EntryGood
  rw [entry_452_checked]
  decide +kernel
theorem good_452 : Good (rowAt 452) := by
  rw [row_452]
  unfold Good
  decide +kernel

def data_453 : RowData := ⟨{(-1, -2), (-1, 0), (0, -2)}, {(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 12⟩
theorem entry_453_checked : entryAt 453 = entry_453 := by
  rw [entry_chunk_22 7 (by decide)]
  decide +kernel
theorem row_453 : rowAt 453 = data_453 := by
  rw [rowAt, dif_neg (by decide : ¬ 453 < 6), entry_453_checked]
  change forkRow [placeRow ⟨359, 0, 4, 3⟩ (rowAt 359), placeRow ⟨226, 7, 3, 1⟩ (rowAt 226), placeRow ⟨386, 4, 2, 4⟩ (rowAt 386), placeRow ⟨389, 1, 5, 4⟩ (rowAt 389), placeRow ⟨414, 4, 3, 3⟩ (rowAt 414)] = data_453
  rw [row_359, row_226, row_386, row_389, row_414]
  apply row_ext <;> decide +kernel
theorem entry_good_453 : EntryGood 453 := by
  unfold EntryGood
  rw [entry_453_checked]
  decide +kernel
theorem good_453 : Good (rowAt 453) := by
  rw [row_453]
  unfold Good
  decide +kernel

def data_454 : RowData := ⟨{(-2, -1), (-1, -1), (-1, 0), (0, -1), (1, -1)}, {(-5, 1), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)}, 19⟩
theorem entry_454_checked : entryAt 454 = entry_454 := by
  rw [entry_chunk_22 8 (by decide)]
  decide +kernel
theorem row_454 : rowAt 454 = data_454 := by
  rw [rowAt, dif_neg (by decide : ¬ 454 < 6), entry_454_checked]
  change forkRow [placeRow ⟨58, 0, 6, 3⟩ (rowAt 58), placeRow ⟨436, 0, 3, 6⟩ (rowAt 436)] = data_454
  rw [row_58, row_436]
  apply row_ext <;> decide +kernel
theorem entry_good_454 : EntryGood 454 := by
  unfold EntryGood
  rw [entry_454_checked]
  decide +kernel
theorem good_454 : Good (rowAt 454) := by
  rw [row_454]
  unfold Good
  decide +kernel

def data_455 : RowData := ⟨{(-3, -1), (-3, 0), (-3, 1), (-2, 1), (-1, 1)}, {(-5, 2), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (2, 0)}, 5⟩
theorem entry_455_checked : entryAt 455 = entry_455 := by
  rw [entry_chunk_22 9 (by decide)]
  decide +kernel
theorem row_455 : rowAt 455 = data_455 := by
  rw [rowAt, dif_neg (by decide : ¬ 455 < 6), entry_455_checked]
  change forkRow [placeRow ⟨20, 2, 4, 5⟩ (rowAt 20), placeRow ⟨118, 3, 0, 5⟩ (rowAt 118), placeRow ⟨39, 2, 3, 4⟩ (rowAt 39)] = data_455
  rw [row_20, row_118, row_39]
  apply row_ext <;> decide +kernel
theorem entry_good_455 : EntryGood 455 := by
  unfold EntryGood
  rw [entry_455_checked]
  decide +kernel
theorem good_455 : Good (rowAt 455) := by
  rw [row_455]
  unfold Good
  decide +kernel

def data_456 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)}, 12⟩
theorem entry_456_checked : entryAt 456 = entry_456 := by
  rw [entry_chunk_22 10 (by decide)]
  decide +kernel
theorem row_456 : rowAt 456 = data_456 := by
  rw [rowAt, dif_neg (by decide : ¬ 456 < 6), entry_456_checked]
  change forkRow [placeRow ⟨308, 4, 4, 3⟩ (rowAt 308), placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55)] = data_456
  rw [row_308, row_64, row_63, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_456 : EntryGood 456 := by
  unfold EntryGood
  rw [entry_456_checked]
  decide +kernel
theorem good_456 : Good (rowAt 456) := by
  rw [row_456]
  unfold Good
  decide +kernel

def data_457 : RowData := ⟨{(-1, -3), (-1, -1), (0, -1), (1, -1), (2, -1)}, {(-4, 1), (-4, 3), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)}, 20⟩
theorem entry_457_checked : entryAt 457 = entry_457 := by
  rw [entry_chunk_22 11 (by decide)]
  decide +kernel
theorem row_457 : rowAt 457 = data_457 := by
  rw [rowAt, dif_neg (by decide : ¬ 457 < 6), entry_457_checked]
  change forkRow [placeRow ⟨28, 7, 3, 2⟩ (rowAt 28), placeRow ⟨454, 0, 5, 4⟩ (rowAt 454)] = data_457
  rw [row_28, row_454]
  apply row_ext <;> decide +kernel
theorem entry_good_457 : EntryGood 457 := by
  unfold EntryGood
  rw [entry_457_checked]
  decide +kernel
theorem good_457 : Good (rowAt 457) := by
  rw [row_457]
  unfold Good
  decide +kernel

def data_458 : RowData := ⟨{(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)}, {(-5, 4), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4)}, 17⟩
theorem entry_458_checked : entryAt 458 = entry_458 := by
  rw [entry_chunk_22 12 (by decide)]
  decide +kernel
theorem row_458 : rowAt 458 = data_458 := by
  rw [rowAt, dif_neg (by decide : ¬ 458 < 6), entry_458_checked]
  change forkRow [placeRow ⟨130, 1, 4, 2⟩ (rowAt 130), placeRow ⟨177, 1, 4, 2⟩ (rowAt 177), placeRow ⟨450, 0, 1, 4⟩ (rowAt 450)] = data_458
  rw [row_130, row_177, row_450]
  apply row_ext <;> decide +kernel
theorem entry_good_458 : EntryGood 458 := by
  unfold EntryGood
  rw [entry_458_checked]
  decide +kernel
theorem good_458 : Good (rowAt 458) := by
  rw [row_458]
  unfold Good
  decide +kernel

def data_459 : RowData := ⟨{(-1, -1), (0, -2), (0, -1), (1, -1), (2, -1)}, {(-4, 1), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -2), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -2), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)}, 20⟩
theorem entry_459_checked : entryAt 459 = entry_459 := by
  rw [entry_chunk_22 13 (by decide)]
  decide +kernel
theorem row_459 : rowAt 459 = data_459 := by
  rw [rowAt, dif_neg (by decide : ¬ 459 < 6), entry_459_checked]
  change forkRow [placeRow ⟨97, 2, 7, 3⟩ (rowAt 97), placeRow ⟨448, 0, 5, 4⟩ (rowAt 448), placeRow ⟨65, 2, 7, 3⟩ (rowAt 65)] = data_459
  rw [row_97, row_448, row_65]
  apply row_ext <;> decide +kernel
theorem entry_good_459 : EntryGood 459 := by
  unfold EntryGood
  rw [entry_459_checked]
  decide +kernel
theorem good_459 : Good (rowAt 459) := by
  rw [row_459]
  unfold Good
  decide +kernel

def data_460 : RowData := ⟨{(-2, 0), (-1, 0)}, {(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 11⟩
theorem entry_460_checked : entryAt 460 = entry_460 := by
  rw [entry_chunk_22 14 (by decide)]
  decide +kernel
theorem row_460 : rowAt 460 = data_460 := by
  rw [rowAt, dif_neg (by decide : ¬ 460 < 6), entry_460_checked]
  change forkRow [placeRow ⟨183, 6, 1, 4⟩ (rowAt 183), placeRow ⟨173, 2, 5, 4⟩ (rowAt 173), placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨282, 4, 1, 4⟩ (rowAt 282), placeRow ⟨246, 2, 5, 4⟩ (rowAt 246), placeRow ⟨263, 2, 5, 4⟩ (rowAt 263), placeRow ⟨220, 2, 5, 4⟩ (rowAt 220)] = data_460
  rw [row_183, row_173, row_295, row_282, row_246, row_263, row_220]
  apply row_ext <;> decide +kernel
theorem entry_good_460 : EntryGood 460 := by
  unfold EntryGood
  rw [entry_460_checked]
  decide +kernel
theorem good_460 : Good (rowAt 460) := by
  rw [row_460]
  unfold Good
  decide +kernel

def data_461 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)}, {(-3, 4), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)}, 18⟩
theorem entry_461_checked : entryAt 461 = entry_461 := by
  rw [entry_chunk_22 15 (by decide)]
  decide +kernel
theorem row_461 : rowAt 461 = data_461 := by
  rw [rowAt, dif_neg (by decide : ¬ 461 < 6), entry_461_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨458, 0, 6, 4⟩ (rowAt 458)] = data_461
  rw [row_4, row_458]
  apply row_ext <;> decide +kernel
theorem entry_good_461 : EntryGood 461 := by
  unfold EntryGood
  rw [entry_461_checked]
  decide +kernel
theorem good_461 : Good (rowAt 461) := by
  rw [row_461]
  unfold Good
  decide +kernel

def data_462 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (-1, 0)}, {(-5, 3), (-5, 5), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)}, 19⟩
theorem entry_462_checked : entryAt 462 = entry_462 := by
  rw [entry_chunk_22 16 (by decide)]
  decide +kernel
theorem row_462 : rowAt 462 = data_462 := by
  rw [rowAt, dif_neg (by decide : ¬ 462 < 6), entry_462_checked]
  change forkRow [placeRow ⟨452, 0, 3, 2⟩ (rowAt 452), placeRow ⟨86, 0, 5, 4⟩ (rowAt 86), placeRow ⟨328, 1, 5, 4⟩ (rowAt 328)] = data_462
  rw [row_452, row_86, row_328]
  apply row_ext <;> decide +kernel
theorem entry_good_462 : EntryGood 462 := by
  unfold EntryGood
  rw [entry_462_checked]
  decide +kernel
theorem good_462 : Good (rowAt 462) := by
  rw [row_462]
  unfold Good
  decide +kernel

def data_463 : RowData := ⟨{(-2, -2), (-2, -1), (-1, -3), (-1, -1), (0, -1), (1, -1)}, {(-5, 1), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -2), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3)}, 20⟩
theorem entry_463_checked : entryAt 463 = entry_463 := by
  rw [entry_chunk_22 17 (by decide)]
  decide +kernel
theorem row_463 : rowAt 463 = data_463 := by
  rw [rowAt, dif_neg (by decide : ¬ 463 < 6), entry_463_checked]
  change forkRow [placeRow ⟨170, 0, 6, 3⟩ (rowAt 170), placeRow ⟨76, 1, 3, 2⟩ (rowAt 76), placeRow ⟨447, 0, 5, 4⟩ (rowAt 447)] = data_463
  rw [row_170, row_76, row_447]
  apply row_ext <;> decide +kernel
theorem entry_good_463 : EntryGood 463 := by
  unfold EntryGood
  rw [entry_463_checked]
  decide +kernel
theorem good_463 : Good (rowAt 463) := by
  rw [row_463]
  unfold Good
  decide +kernel

def data_464 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2)}, {(-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 4), (7, 5)}, 19⟩
theorem entry_464_checked : entryAt 464 = entry_464 := by
  rw [entry_chunk_22 18 (by decide)]
  decide +kernel
theorem row_464 : rowAt 464 = data_464 := by
  rw [rowAt, dif_neg (by decide : ¬ 464 < 6), entry_464_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨224, 0, 5, 4⟩ (rowAt 224), placeRow ⟨315, 0, 7, 3⟩ (rowAt 315), placeRow ⟨306, 0, 5, 5⟩ (rowAt 306), placeRow ⟨358, 0, 7, 3⟩ (rowAt 358), placeRow ⟨461, 0, 5, 5⟩ (rowAt 461)] = data_464
  rw [row_63, row_224, row_315, row_306, row_358, row_461]
  apply row_ext <;> decide +kernel
theorem entry_good_464 : EntryGood 464 := by
  unfold EntryGood
  rw [entry_464_checked]
  decide +kernel
theorem good_464 : Good (rowAt 464) := by
  rw [row_464]
  unfold Good
  decide +kernel

def data_465 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 10⟩
theorem entry_465_checked : entryAt 465 = entry_465 := by
  rw [entry_chunk_22 19 (by decide)]
  decide +kernel
theorem row_465 : rowAt 465 = data_465 := by
  rw [rowAt, dif_neg (by decide : ¬ 465 < 6), entry_465_checked]
  change forkRow [placeRow ⟨55, 3, 4, 5⟩ (rowAt 55), placeRow ⟨285, 0, 3, 4⟩ (rowAt 285), placeRow ⟨64, 1, 3, 1⟩ (rowAt 64)] = data_465
  rw [row_55, row_285, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_465 : EntryGood 465 := by
  unfold EntryGood
  rw [entry_465_checked]
  decide +kernel
theorem good_465 : Good (rowAt 465) := by
  rw [row_465]
  unfold Good
  decide +kernel

def data_466 : RowData := ⟨{(-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2)}, {(-7, -1), (-7, 0), (-7, 1), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 3), (-3, 4), (-3, 5), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0), (5, 1), (5, 2)}, 14⟩
theorem entry_466_checked : entryAt 466 = entry_466 := by
  rw [entry_chunk_23 0 (by decide)]
  decide +kernel
theorem row_466 : rowAt 466 = data_466 := by
  rw [rowAt, dif_neg (by decide : ¬ 466 < 6), entry_466_checked]
  change forkRow [placeRow ⟨395, 4, 3, 4⟩ (rowAt 395), placeRow ⟨360, 4, 2, 6⟩ (rowAt 360), placeRow ⟨417, 1, 5, 4⟩ (rowAt 417), placeRow ⟨325, 4, 3, 4⟩ (rowAt 325), placeRow ⟨324, 4, 3, 5⟩ (rowAt 324)] = data_466
  rw [row_395, row_360, row_417, row_325, row_324]
  apply row_ext <;> decide +kernel
theorem entry_good_466 : EntryGood 466 := by
  unfold EntryGood
  rw [entry_466_checked]
  decide +kernel
theorem good_466 : Good (rowAt 466) := by
  rw [row_466]
  unfold Good
  decide +kernel

def data_467 : RowData := ⟨{(0, 1), (0, 2), (0, 3)}, {(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 0), (8, 1), (8, 2), (9, 0), (9, 2)}, 21⟩
theorem entry_467_checked : entryAt 467 = entry_467 := by
  rw [entry_chunk_23 1 (by decide)]
  decide +kernel
theorem row_467 : rowAt 467 = data_467 := by
  rw [rowAt, dif_neg (by decide : ¬ 467 < 6), entry_467_checked]
  change forkRow [placeRow ⟨64, 7, 5, 7⟩ (rowAt 64), placeRow ⟨314, 6, 5, 4⟩ (rowAt 314), placeRow ⟨443, 1, 5, 7⟩ (rowAt 443)] = data_467
  rw [row_64, row_314, row_443]
  apply row_ext <;> decide +kernel
theorem entry_good_467 : EntryGood 467 := by
  unfold EntryGood
  rw [entry_467_checked]
  decide +kernel
theorem good_467 : Good (rowAt 467) := by
  rw [row_467]
  unfold Good
  decide +kernel

def data_468 : RowData := ⟨{(0, 1), (0, 2), (1, 1), (2, 1), (3, 1)}, {(-2, 8), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 5), (7, 6), (7, 7), (7, 8)}, 20⟩
theorem entry_468_checked : entryAt 468 = entry_468 := by
  rw [entry_chunk_23 2 (by decide)]
  decide +kernel
theorem row_468 : rowAt 468 = data_468 := by
  rw [rowAt, dif_neg (by decide : ¬ 468 < 6), entry_468_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨464, 0, 4, 7⟩ (rowAt 464)] = data_468
  rw [row_6, row_464]
  apply row_ext <;> decide +kernel
theorem entry_good_468 : EntryGood 468 := by
  unfold EntryGood
  rw [entry_468_checked]
  decide +kernel
theorem good_468 : Good (rowAt 468) := by
  rw [row_468]
  unfold Good
  decide +kernel

def data_469 : RowData := ⟨{(0, 1), (0, 2), (0, 3)}, {(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 0), (8, 1), (8, 2), (9, 0), (9, 2)}, 21⟩
theorem entry_469_checked : entryAt 469 = entry_469 := by
  rw [entry_chunk_23 3 (by decide)]
  decide +kernel
theorem row_469 : rowAt 469 = data_469 := by
  rw [rowAt, dif_neg (by decide : ¬ 469 < 6), entry_469_checked]
  change forkRow [placeRow ⟨55, 5, 4, 3⟩ (rowAt 55), placeRow ⟨443, 1, 5, 7⟩ (rowAt 443), placeRow ⟨314, 6, 5, 4⟩ (rowAt 314)] = data_469
  rw [row_55, row_443, row_314]
  apply row_ext <;> decide +kernel
theorem entry_good_469 : EntryGood 469 := by
  unfold EntryGood
  rw [entry_469_checked]
  decide +kernel
theorem good_469 : Good (rowAt 469) := by
  rw [row_469]
  unfold Good
  decide +kernel

def data_470 : RowData := ⟨{(0, -1), (1, -1), (2, -1), (3, -1)}, {(-2, 6), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 3), (7, 4), (7, 5), (7, 6)}, 21⟩
theorem entry_470_checked : entryAt 470 = entry_470 := by
  rw [entry_chunk_23 4 (by decide)]
  decide +kernel
theorem row_470 : rowAt 470 = data_470 := by
  rw [rowAt, dif_neg (by decide : ¬ 470 < 6), entry_470_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨468, 0, 4, 2⟩ (rowAt 468)] = data_470
  rw [row_6, row_468]
  apply row_ext <;> decide +kernel
theorem entry_good_470 : EntryGood 470 := by
  unfold EntryGood
  rw [entry_470_checked]
  decide +kernel
theorem good_470 : Good (rowAt 470) := by
  rw [row_470]
  unfold Good
  decide +kernel

def data_471 : RowData := ⟨{(-1, 0), (-1, 1), (-1, 2), (-1, 3)}, {(-6, 1), (-6, 2), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 1), (-2, 2), (-2, 3), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)}, 15⟩
theorem entry_471_checked : entryAt 471 = entry_471 := by
  rw [entry_chunk_23 5 (by decide)]
  decide +kernel
theorem row_471 : rowAt 471 = data_471 := by
  rw [rowAt, dif_neg (by decide : ¬ 471 < 6), entry_471_checked]
  change forkRow [placeRow ⟨6, 5, 4, 3⟩ (rowAt 6), placeRow ⟨466, 0, 5, 6⟩ (rowAt 466)] = data_471
  rw [row_6, row_466]
  apply row_ext <;> decide +kernel
theorem entry_good_471 : EntryGood 471 := by
  unfold EntryGood
  rw [entry_471_checked]
  decide +kernel
theorem good_471 : Good (rowAt 471) := by
  rw [row_471]
  unfold Good
  decide +kernel

def data_472 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3)}, {(-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (6, 1), (7, -2), (7, -1), (7, 0), (7, 1)}, 15⟩
theorem entry_472_checked : entryAt 472 = entry_472 := by
  rw [entry_chunk_23 6 (by decide)]
  decide +kernel
theorem row_472 : rowAt 472 = data_472 := by
  rw [rowAt, dif_neg (by decide : ¬ 472 < 6), entry_472_checked]
  change forkRow [placeRow ⟨6, 5, 5, 0⟩ (rowAt 6), placeRow ⟨466, 0, 6, 3⟩ (rowAt 466)] = data_472
  rw [row_6, row_466]
  apply row_ext <;> decide +kernel
theorem entry_good_472 : EntryGood 472 := by
  unfold EntryGood
  rw [entry_472_checked]
  decide +kernel
theorem good_472 : Good (rowAt 472) := by
  rw [row_472]
  unfold Good
  decide +kernel

def data_473 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0), (-1, 1), (0, 1)}, {(-6, 2), (-6, 4), (-5, 2), (-5, 3), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4)}, 20⟩
theorem entry_473_checked : entryAt 473 = entry_473 := by
  rw [entry_chunk_23 7 (by decide)]
  decide +kernel
theorem row_473 : rowAt 473 = data_473 := by
  rw [rowAt, dif_neg (by decide : ¬ 473 < 6), entry_473_checked]
  change forkRow [placeRow ⟨121, 5, 5, 4⟩ (rowAt 121), placeRow ⟨436, 0, 3, 7⟩ (rowAt 436), placeRow ⟨445, 4, 5, 4⟩ (rowAt 445)] = data_473
  rw [row_121, row_436, row_445]
  apply row_ext <;> decide +kernel
theorem entry_good_473 : EntryGood 473 := by
  unfold EntryGood
  rw [entry_473_checked]
  decide +kernel
theorem good_473 : Good (rowAt 473) := by
  rw [row_473]
  unfold Good
  decide +kernel

def data_474 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (1, 0), (2, 0), (3, 0)}, {(-3, 2), (-3, 4), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -1), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 4)}, 21⟩
theorem entry_474_checked : entryAt 474 = entry_474 := by
  rw [entry_chunk_23 8 (by decide)]
  decide +kernel
theorem row_474 : rowAt 474 = data_474 := by
  rw [rowAt, dif_neg (by decide : ¬ 474 < 6), entry_474_checked]
  change forkRow [placeRow ⟨463, 0, 6, 5⟩ (rowAt 463), placeRow ⟨70, 0, 3, 5⟩ (rowAt 70), placeRow ⟨83, 1, 5, 3⟩ (rowAt 83)] = data_474
  rw [row_463, row_70, row_83]
  apply row_ext <;> decide +kernel
theorem entry_good_474 : EntryGood 474 := by
  unfold EntryGood
  rw [entry_474_checked]
  decide +kernel
theorem good_474 : Good (rowAt 474) := by
  rw [row_474]
  unfold Good
  decide +kernel

def data_475 : RowData := ⟨{(-3, -2), (-3, 0), (-2, 0), (-1, 0)}, {(-6, 2), (-6, 4), (-5, 2), (-5, 3), (-5, 4), (-4, -1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (4, 4)}, 21⟩
theorem entry_475_checked : entryAt 475 = entry_475 := by
  rw [entry_chunk_23 9 (by decide)]
  decide +kernel
theorem row_475 : rowAt 475 = data_475 := by
  rw [rowAt, dif_neg (by decide : ¬ 475 < 6), entry_475_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨261, 1, 4, 3⟩ (rowAt 261), placeRow ⟨457, 0, 2, 5⟩ (rowAt 457), placeRow ⟨269, 2, 2, 5⟩ (rowAt 269)] = data_475
  rw [row_63, row_261, row_457, row_269]
  apply row_ext <;> decide +kernel
theorem entry_good_475 : EntryGood 475 := by
  unfold EntryGood
  rw [entry_475_checked]
  decide +kernel
theorem good_475 : Good (rowAt 475) := by
  rw [row_475]
  unfold Good
  decide +kernel

def data_476 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, 0)}, {(-5, 1), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -2), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -2), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)}, 21⟩
theorem entry_476_checked : entryAt 476 = entry_476 := by
  rw [entry_chunk_23 10 (by decide)]
  decide +kernel
theorem row_476 : rowAt 476 = data_476 := by
  rw [rowAt, dif_neg (by decide : ¬ 476 < 6), entry_476_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨473, 0, 5, 3⟩ (rowAt 473)] = data_476
  rw [row_0, row_473]
  apply row_ext <;> decide +kernel
theorem entry_good_476 : EntryGood 476 := by
  unfold EntryGood
  rw [entry_476_checked]
  decide +kernel
theorem good_476 : Good (rowAt 476) := by
  rw [row_476]
  unfold Good
  decide +kernel

def data_477 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-5, -3), (-5, -2), (-5, -1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-1, -7), (-1, -6), (-1, -5), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -4), (6, -3), (6, -2), (6, -1), (7, -4), (7, -3), (7, -2), (7, -1)}, 16⟩
theorem entry_477_checked : entryAt 477 = entry_477 := by
  rw [entry_chunk_23 11 (by decide)]
  decide +kernel
theorem row_477 : rowAt 477 = data_477 := by
  rw [rowAt, dif_neg (by decide : ¬ 477 < 6), entry_477_checked]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (rowAt 55), placeRow ⟨154, 7, 4, 5⟩ (rowAt 154), placeRow ⟨154, 3, 4, 0⟩ (rowAt 154), placeRow ⟨471, 2, 5, 4⟩ (rowAt 471)] = data_477
  rw [row_55, row_154, row_471]
  apply row_ext <;> decide +kernel
theorem entry_good_477 : EntryGood 477 := by
  unfold EntryGood
  rw [entry_477_checked]
  decide +kernel
theorem good_477 : Good (rowAt 477) := by
  rw [row_477]
  unfold Good
  decide +kernel

def data_478 : RowData := ⟨{(1, -2), (1, -1), (1, 0), (2, 0)}, {(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)}, 8⟩
theorem entry_478_checked : entryAt 478 = entry_478 := by
  rw [entry_chunk_23 12 (by decide)]
  decide +kernel
theorem row_478 : rowAt 478 = data_478 := by
  rw [rowAt, dif_neg (by decide : ¬ 478 < 6), entry_478_checked]
  change forkRow [placeRow ⟨25, 3, 4, 5⟩ (rowAt 25), placeRow ⟨165, 2, 4, 5⟩ (rowAt 165), placeRow ⟨190, 0, 7, 4⟩ (rowAt 190)] = data_478
  rw [row_25, row_165, row_190]
  apply row_ext <;> decide +kernel
theorem entry_good_478 : EntryGood 478 := by
  unfold EntryGood
  rw [entry_478_checked]
  decide +kernel
theorem good_478 : Good (rowAt 478) := by
  rw [row_478]
  unfold Good
  decide +kernel

def data_479 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4)}, 21⟩
theorem entry_479_checked : entryAt 479 = entry_479 := by
  rw [entry_chunk_23 13 (by decide)]
  decide +kernel
theorem row_479 : rowAt 479 = data_479 := by
  rw [rowAt, dif_neg (by decide : ¬ 479 < 6), entry_479_checked]
  change forkRow [placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨443, 0, 4, 5⟩ (rowAt 443), placeRow ⟨443, 4, 1, 5⟩ (rowAt 443)] = data_479
  rw [row_55, row_443]
  apply row_ext <;> decide +kernel
theorem entry_good_479 : EntryGood 479 := by
  unfold EntryGood
  rw [entry_479_checked]
  decide +kernel
theorem good_479 : Good (rowAt 479) := by
  rw [row_479]
  unfold Good
  decide +kernel

#check row_479
def data_480 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (0, -1), (1, 1)}, {(-1, -3), (-1, -2), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3)}, 7⟩
theorem entry_480_checked : entryAt 480 = entry_480 := by
  rw [entry_chunk_23 14 (by decide)]
  decide +kernel
theorem row_480 : rowAt 480 = data_480 := by
  rw [rowAt, dif_neg (by decide : ¬ 480 < 6), entry_480_checked]
  change forkRow [placeRow ⟨108, 1, 4, 5⟩ (rowAt 108), placeRow ⟨4, 1, 5, 4⟩ (rowAt 4)] = data_480
  rw [row_108, row_4]
  apply row_ext <;> decide +kernel
theorem entry_good_480 : EntryGood 480 := by
  unfold EntryGood
  rw [entry_480_checked]
  decide +kernel
theorem good_480 : Good (rowAt 480) := by
  rw [row_480]
  unfold Good
  decide +kernel

def data_481 : RowData := ⟨{(-3, -2), (-2, 0), (-2, 1), (-1, 0)}, {(-5, 0), (-4, -1), (-4, 0), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (4, 2)}, 11⟩
theorem entry_481_checked : entryAt 481 = entry_481 := by
  rw [entry_chunk_23 15 (by decide)]
  decide +kernel
theorem row_481 : rowAt 481 = data_481 := by
  rw [rowAt, dif_neg (by decide : ¬ 481 < 6), entry_481_checked]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (rowAt 303), placeRow ⟨429, 2, 1, 4⟩ (rowAt 429), placeRow ⟨309, 1, 1, 4⟩ (rowAt 309), placeRow ⟨206, 2, 1, 4⟩ (rowAt 206), placeRow ⟨169, 2, 1, 4⟩ (rowAt 169), placeRow ⟨207, 2, 1, 4⟩ (rowAt 207)] = data_481
  rw [row_303, row_429, row_309, row_206, row_169, row_207]
  apply row_ext <;> decide +kernel
theorem entry_good_481 : EntryGood 481 := by
  unfold EntryGood
  rw [entry_481_checked]
  decide +kernel
theorem good_481 : Good (rowAt 481) := by
  rw [row_481]
  unfold Good
  decide +kernel

def data_482 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -3)}, {(-3, -1), (-2, -2), (-2, -1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -1)}, 7⟩
theorem entry_482_checked : entryAt 482 = entry_482 := by
  rw [entry_chunk_23 16 (by decide)]
  decide +kernel
theorem row_482 : rowAt 482 = data_482 := by
  rw [rowAt, dif_neg (by decide : ¬ 482 < 6), entry_482_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨218, 2, 4, 3⟩ (rowAt 218)] = data_482
  rw [row_6, row_218]
  apply row_ext <;> decide +kernel
theorem entry_good_482 : EntryGood 482 := by
  unfold EntryGood
  rw [entry_482_checked]
  decide +kernel
theorem good_482 : Good (rowAt 482) := by
  rw [row_482]
  unfold Good
  decide +kernel

def data_483 : RowData := ⟨{(-2, -3), (-2, -2), (-2, -1), (0, -2), (0, -1)}, {(-7, -1), (-6, -2), (-6, -1), (-5, -2), (-5, -1), (-4, -2), (-4, -1), (-3, -2), (-3, -1), (-2, -3), (-2, -2), (-2, -1), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (8, -3), (8, -2), (8, -1), (9, -3), (9, -1)}, 22⟩
theorem entry_483_checked : entryAt 483 = entry_483 := by
  rw [entry_chunk_23 17 (by decide)]
  decide +kernel
theorem row_483 : rowAt 483 = data_483 := by
  rw [rowAt, dif_neg (by decide : ¬ 483 < 6), entry_483_checked]
  change forkRow [placeRow ⟨173, 1, 4, 5⟩ (rowAt 173), placeRow ⟨292, 7, 3, 1⟩ (rowAt 292), placeRow ⟨319, 1, 3, 5⟩ (rowAt 319), placeRow ⟨192, 6, 4, 1⟩ (rowAt 192), placeRow ⟨475, 1, 4, 5⟩ (rowAt 475)] = data_483
  rw [row_173, row_292, row_319, row_192, row_475]
  apply row_ext <;> decide +kernel
theorem entry_good_483 : EntryGood 483 := by
  unfold EntryGood
  rw [entry_483_checked]
  decide +kernel
theorem good_483 : Good (rowAt 483) := by
  rw [row_483]
  unfold Good
  decide +kernel

def data_484 : RowData := ⟨{(-2, 0), (-2, 1), (-1, 0)}, {(-5, 1), (-4, -1), (-4, 1), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 12⟩
theorem entry_484_checked : entryAt 484 = entry_484 := by
  rw [entry_chunk_23 18 (by decide)]
  decide +kernel
theorem row_484 : rowAt 484 = data_484 := by
  rw [rowAt, dif_neg (by decide : ¬ 484 < 6), entry_484_checked]
  change forkRow [placeRow ⟨25, 4, 1, 5⟩ (rowAt 25), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107), placeRow ⟨349, 3, 1, 5⟩ (rowAt 349), placeRow ⟨163, 2, 5, 4⟩ (rowAt 163)] = data_484
  rw [row_25, row_107, row_349, row_163]
  apply row_ext <;> decide +kernel
theorem entry_good_484 : EntryGood 484 := by
  unfold EntryGood
  rw [entry_484_checked]
  decide +kernel
theorem good_484 : Good (rowAt 484) := by
  rw [row_484]
  unfold Good
  decide +kernel

def data_485 : RowData := ⟨{(-1, 0), (-1, 1), (0, -3), (0, -2)}, {(-4, 1), (-3, -1), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 13⟩
theorem entry_485_checked : entryAt 485 = entry_485 := by
  rw [entry_chunk_23 19 (by decide)]
  decide +kernel
theorem row_485 : rowAt 485 = data_485 := by
  rw [rowAt, dif_neg (by decide : ¬ 485 < 6), entry_485_checked]
  change forkRow [placeRow ⟨484, 0, 5, 4⟩ (rowAt 484), placeRow ⟨2, 3, 4, 3⟩ (rowAt 2)] = data_485
  rw [row_484, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_485 : EntryGood 485 := by
  unfold EntryGood
  rw [entry_485_checked]
  decide +kernel
theorem good_485 : Good (rowAt 485) := by
  rw [row_485]
  unfold Good
  decide +kernel

def data_486 : RowData := ⟨{(0, -3), (0, -1), (1, -4), (1, -3)}, {(-3, 0), (-2, -2), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1), (4, 0), (5, -2), (5, 0)}, 14⟩
theorem entry_486_checked : entryAt 486 = entry_486 := by
  rw [entry_chunk_24 0 (by decide)]
  decide +kernel
theorem row_486 : rowAt 486 = data_486 := by
  rw [rowAt, dif_neg (by decide : ¬ 486 < 6), entry_486_checked]
  change forkRow [placeRow ⟨2, 5, 4, 2⟩ (rowAt 2), placeRow ⟨485, 0, 5, 3⟩ (rowAt 485)] = data_486
  rw [row_2, row_485]
  apply row_ext <;> decide +kernel
theorem entry_good_486 : EntryGood 486 := by
  unfold EntryGood
  rw [entry_486_checked]
  decide +kernel
theorem good_486 : Good (rowAt 486) := by
  rw [row_486]
  unfold Good
  decide +kernel

def data_487 : RowData := ⟨{(-2, -2), (-1, 0), (-1, 1), (0, -3), (0, -2)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (5, 2)}, 12⟩
theorem entry_487_checked : entryAt 487 = entry_487 := by
  rw [entry_chunk_24 1 (by decide)]
  decide +kernel
theorem row_487 : rowAt 487 = data_487 := by
  rw [rowAt, dif_neg (by decide : ¬ 487 < 6), entry_487_checked]
  change forkRow [placeRow ⟨2, 3, 4, 3⟩ (rowAt 2), placeRow ⟨481, 0, 5, 4⟩ (rowAt 481)] = data_487
  rw [row_2, row_481]
  apply row_ext <;> decide +kernel
theorem entry_good_487 : EntryGood 487 := by
  unfold EntryGood
  rw [entry_487_checked]
  decide +kernel
theorem good_487 : Good (rowAt 487) := by
  rw [row_487]
  unfold Good
  decide +kernel

def data_488 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 0)}, {(-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (2, 1)}, 9⟩
theorem entry_488_checked : entryAt 488 = entry_488 := by
  rw [entry_chunk_24 2 (by decide)]
  decide +kernel
theorem row_488 : rowAt 488 = data_488 := by
  rw [rowAt, dif_neg (by decide : ¬ 488 < 6), entry_488_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨247, 0, 2, 5⟩ (rowAt 247)] = data_488
  rw [row_0, row_247]
  apply row_ext <;> decide +kernel
theorem entry_good_488 : EntryGood 488 := by
  unfold EntryGood
  rw [entry_488_checked]
  decide +kernel
theorem good_488 : Good (rowAt 488) := by
  rw [row_488]
  unfold Good
  decide +kernel

def data_489 : RowData := ⟨{(-2, -2), (-2, 0), (-1, -2), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 9⟩
theorem entry_489_checked : entryAt 489 = entry_489 := by
  rw [entry_chunk_24 3 (by decide)]
  decide +kernel
theorem row_489 : rowAt 489 = data_489 := by
  rw [rowAt, dif_neg (by decide : ¬ 489 < 6), entry_489_checked]
  change forkRow [placeRow ⟨356, 1, 3, 3⟩ (rowAt 356), placeRow ⟨197, 4, 1, 4⟩ (rowAt 197), placeRow ⟨172, 6, 1, 4⟩ (rowAt 172)] = data_489
  rw [row_356, row_197, row_172]
  apply row_ext <;> decide +kernel
theorem entry_good_489 : EntryGood 489 := by
  unfold EntryGood
  rw [entry_489_checked]
  decide +kernel
theorem good_489 : Good (rowAt 489) := by
  rw [row_489]
  unfold Good
  decide +kernel

def data_490 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -4), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -1), (9, 0), (9, 1), (9, 2), (10, -1), (10, 0), (10, 1), (10, 2)}, 22⟩
theorem entry_490_checked : entryAt 490 = entry_490 := by
  rw [entry_chunk_24 4 (by decide)]
  decide +kernel
theorem row_490 : rowAt 490 = data_490 := by
  rw [rowAt, dif_neg (by decide : ¬ 490 < 6), entry_490_checked]
  change forkRow [placeRow ⟨64, 1, 3, 1⟩ (rowAt 64), placeRow ⟨471, 0, 5, 1⟩ (rowAt 471), placeRow ⟨470, 1, 5, 1⟩ (rowAt 470), placeRow ⟨111, 0, 3, 1⟩ (rowAt 111)] = data_490
  rw [row_64, row_471, row_470, row_111]
  apply row_ext <;> decide +kernel
theorem entry_good_490 : EntryGood 490 := by
  unfold EntryGood
  rw [entry_490_checked]
  decide +kernel
theorem good_490 : Good (rowAt 490) := by
  rw [row_490]
  unfold Good
  decide +kernel

def data_491 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1)}, {(-3, 0), (-2, 0), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 9⟩
theorem entry_491_checked : entryAt 491 = entry_491 := by
  rw [entry_chunk_24 5 (by decide)]
  decide +kernel
theorem row_491 : rowAt 491 = data_491 := by
  rw [rowAt, dif_neg (by decide : ¬ 491 < 6), entry_491_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨273, 0, 5, 4⟩ (rowAt 273)] = data_491
  rw [row_6, row_273]
  apply row_ext <;> decide +kernel
theorem entry_good_491 : EntryGood 491 := by
  unfold EntryGood
  rw [entry_491_checked]
  decide +kernel
theorem good_491 : Good (rowAt 491) := by
  rw [row_491]
  unfold Good
  decide +kernel

def data_492 : RowData := ⟨{(1, 0), (1, 2), (1, 3), (2, -1), (2, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 3), (6, 4), (7, 4)}, 13⟩
theorem entry_492_checked : entryAt 492 = entry_492 := by
  rw [entry_chunk_24 6 (by decide)]
  decide +kernel
theorem row_492 : rowAt 492 = data_492 := by
  rw [rowAt, dif_neg (by decide : ¬ 492 < 6), entry_492_checked]
  change forkRow [placeRow ⟨62, 4, 3, 4⟩ (rowAt 62), placeRow ⟨107, 4, 3, 4⟩ (rowAt 107), placeRow ⟨487, 0, 6, 6⟩ (rowAt 487)] = data_492
  rw [row_62, row_107, row_487]
  apply row_ext <;> decide +kernel
theorem entry_good_492 : EntryGood 492 := by
  unfold EntryGood
  rw [entry_492_checked]
  decide +kernel
theorem good_492 : Good (rowAt 492) := by
  rw [row_492]
  unfold Good
  decide +kernel

def data_493 : RowData := ⟨{(-2, -2), (-2, -1), (-2, 0), (-1, 0)}, {(-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, 1)}, 8⟩
theorem entry_493_checked : entryAt 493 = entry_493 := by
  rw [entry_chunk_24 7 (by decide)]
  decide +kernel
theorem row_493 : rowAt 493 = data_493 := by
  rw [rowAt, dif_neg (by decide : ¬ 493 < 6), entry_493_checked]
  change forkRow [placeRow ⟨225, 0, 1, 4⟩ (rowAt 225), placeRow ⟨455, 0, 5, 3⟩ (rowAt 455), placeRow ⟨236, 1, 5, 5⟩ (rowAt 236), placeRow ⟨221, 0, 5, 4⟩ (rowAt 221)] = data_493
  rw [row_225, row_455, row_236, row_221]
  apply row_ext <;> decide +kernel
theorem entry_good_493 : EntryGood 493 := by
  unfold EntryGood
  rw [entry_493_checked]
  decide +kernel
theorem good_493 : Good (rowAt 493) := by
  rw [row_493]
  unfold Good
  decide +kernel

def data_494 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0), (-1, 1)}, {(-6, 2), (-5, 2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)}, 11⟩
theorem entry_494_checked : entryAt 494 = entry_494 := by
  rw [entry_chunk_24 8 (by decide)]
  decide +kernel
theorem row_494 : rowAt 494 = data_494 := by
  rw [rowAt, dif_neg (by decide : ¬ 494 < 6), entry_494_checked]
  change forkRow [placeRow ⟨297, 4, 4, 5⟩ (rowAt 297), placeRow ⟨268, 4, 1, 5⟩ (rowAt 268), placeRow ⟨162, 5, 5, 4⟩ (rowAt 162)] = data_494
  rw [row_297, row_268, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_494 : EntryGood 494 := by
  unfold EntryGood
  rw [entry_494_checked]
  decide +kernel
theorem good_494 : Good (rowAt 494) := by
  rw [row_494]
  unfold Good
  decide +kernel

def data_495 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (-1, 0)}, {(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 3), (2, 0), (2, 1)}, 13⟩
theorem entry_495_checked : entryAt 495 = entry_495 := by
  rw [entry_chunk_24 9 (by decide)]
  decide +kernel
theorem row_495 : rowAt 495 = data_495 := by
  rw [rowAt, dif_neg (by decide : ¬ 495 < 6), entry_495_checked]
  change forkRow [placeRow ⟨25, 6, 1, 3⟩ (rowAt 25), placeRow ⟨167, 4, 1, 4⟩ (rowAt 167), placeRow ⟨456, 4, 1, 4⟩ (rowAt 456)] = data_495
  rw [row_25, row_167, row_456]
  apply row_ext <;> decide +kernel
theorem entry_good_495 : EntryGood 495 := by
  unfold EntryGood
  rw [entry_495_checked]
  decide +kernel
theorem good_495 : Good (rowAt 495) := by
  rw [row_495]
  unfold Good
  decide +kernel

def data_496 : RowData := ⟨{(1, 0), (2, 0), (2, 1)}, {(-3, -1), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, 1)}, 12⟩
theorem entry_496_checked : entryAt 496 = entry_496 := by
  rw [entry_chunk_24 10 (by decide)]
  decide +kernel
theorem row_496 : rowAt 496 = data_496 := by
  rw [rowAt, dif_neg (by decide : ¬ 496 < 6), entry_496_checked]
  change forkRow [placeRow ⟨25, 0, 7, 5⟩ (rowAt 25), placeRow ⟨107, 6, 3, 4⟩ (rowAt 107), placeRow ⟨163, 6, 3, 4⟩ (rowAt 163), placeRow ⟨494, 0, 7, 4⟩ (rowAt 494)] = data_496
  rw [row_25, row_107, row_163, row_494]
  apply row_ext <;> decide +kernel
theorem entry_good_496 : EntryGood 496 := by
  unfold EntryGood
  rw [entry_496_checked]
  decide +kernel
theorem good_496 : Good (rowAt 496) := by
  rw [row_496]
  unfold Good
  decide +kernel

def data_497 : RowData := ⟨{(1, -1), (1, 0), (2, -1), (2, 0)}, {(-3, 1), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1), (6, 2), (6, 3), (7, 1)}, 15⟩
theorem entry_497_checked : entryAt 497 = entry_497 := by
  rw [entry_chunk_24 11 (by decide)]
  decide +kernel
theorem row_497 : rowAt 497 = data_497 := by
  rw [rowAt, dif_neg (by decide : ¬ 497 < 6), entry_497_checked]
  change forkRow [placeRow ⟨36, 2, 3, 4⟩ (rowAt 36), placeRow ⟨167, 0, 7, 4⟩ (rowAt 167), placeRow ⟨410, 0, 7, 3⟩ (rowAt 410)] = data_497
  rw [row_36, row_167, row_410]
  apply row_ext <;> decide +kernel
theorem entry_good_497 : EntryGood 497 := by
  unfold EntryGood
  rw [entry_497_checked]
  decide +kernel
theorem good_497 : Good (rowAt 497) := by
  rw [row_497]
  unfold Good
  decide +kernel

def data_498 : RowData := ⟨{(-2, 1), (-1, -2), (-1, -1), (-1, 0), (0, 1)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, 1)}, 9⟩
theorem entry_498_checked : entryAt 498 = entry_498 := by
  rw [entry_chunk_24 12 (by decide)]
  decide +kernel
theorem row_498 : rowAt 498 = data_498 := by
  rw [rowAt, dif_neg (by decide : ¬ 498 < 6), entry_498_checked]
  change forkRow [placeRow ⟨14, 1, 4, 6⟩ (rowAt 14), placeRow ⟨298, 2, 2, 4⟩ (rowAt 298)] = data_498
  rw [row_14, row_298]
  apply row_ext <;> decide +kernel
theorem entry_good_498 : EntryGood 498 := by
  unfold EntryGood
  rw [entry_498_checked]
  decide +kernel
theorem good_498 : Good (rowAt 498) := by
  rw [row_498]
  unfold Good
  decide +kernel

def data_499 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0)}, {(-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)}, 9⟩
theorem entry_499_checked : entryAt 499 = entry_499 := by
  rw [entry_chunk_24 13 (by decide)]
  decide +kernel
theorem row_499 : rowAt 499 = data_499 := by
  rw [rowAt, dif_neg (by decide : ¬ 499 < 6), entry_499_checked]
  change forkRow [placeRow ⟨493, 0, 5, 4⟩ (rowAt 493), placeRow ⟨25, 1, 4, 5⟩ (rowAt 25), placeRow ⟨478, 0, 2, 4⟩ (rowAt 478)] = data_499
  rw [row_493, row_25, row_478]
  apply row_ext <;> decide +kernel
theorem entry_good_499 : EntryGood 499 := by
  unfold EntryGood
  rw [entry_499_checked]
  decide +kernel
theorem good_499 : Good (rowAt 499) := by
  rw [row_499]
  unfold Good
  decide +kernel

def data_500 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, -1)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 12⟩
theorem entry_500_checked : entryAt 500 = entry_500 := by
  rw [entry_chunk_24 14 (by decide)]
  decide +kernel
theorem row_500 : rowAt 500 = data_500 := by
  rw [rowAt, dif_neg (by decide : ¬ 500 < 6), entry_500_checked]
  change forkRow [placeRow ⟨1, 5, 3, 6⟩ (rowAt 1), placeRow ⟨351, 0, 5, 4⟩ (rowAt 351)] = data_500
  rw [row_1, row_351]
  apply row_ext <;> decide +kernel
theorem entry_good_500 : EntryGood 500 := by
  unfold EntryGood
  rw [entry_500_checked]
  decide +kernel
theorem good_500 : Good (rowAt 500) := by
  rw [row_500]
  unfold Good
  decide +kernel

def data_501 : RowData := ⟨{(-3, 0), (-3, 1), (-3, 2), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 1), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 3), (1, 4), (1, 5)}, 10⟩
theorem entry_501_checked : entryAt 501 = entry_501 := by
  rw [entry_chunk_24 15 (by decide)]
  decide +kernel
theorem row_501 : rowAt 501 = data_501 := by
  rw [rowAt, dif_neg (by decide : ¬ 501 < 6), entry_501_checked]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (rowAt 6), placeRow ⟨316, 0, 1, 3⟩ (rowAt 316)] = data_501
  rw [row_6, row_316]
  apply row_ext <;> decide +kernel
theorem entry_good_501 : EntryGood 501 := by
  unfold EntryGood
  rw [entry_501_checked]
  decide +kernel
theorem good_501 : Good (rowAt 501) := by
  rw [row_501]
  unfold Good
  decide +kernel

def data_502 : RowData := ⟨{(-2, -2), (-2, 0), (-1, -2), (-1, 0), (0, -2)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -5), (-3, -4), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 8⟩
theorem entry_502_checked : entryAt 502 = entry_502 := by
  rw [entry_chunk_24 16 (by decide)]
  decide +kernel
theorem row_502 : rowAt 502 = data_502 := by
  rw [rowAt, dif_neg (by decide : ¬ 502 < 6), entry_502_checked]
  change forkRow [placeRow ⟨215, 6, 2, 3⟩ (rowAt 215), placeRow ⟨232, 0, 4, 3⟩ (rowAt 232), placeRow ⟨192, 7, 1, 4⟩ (rowAt 192), placeRow ⟨173, 0, 5, 4⟩ (rowAt 173), placeRow ⟨271, 2, 2, 3⟩ (rowAt 271)] = data_502
  rw [row_215, row_232, row_192, row_173, row_271]
  apply row_ext <;> decide +kernel
theorem entry_good_502 : EntryGood 502 := by
  unfold EntryGood
  rw [entry_502_checked]
  decide +kernel
theorem good_502 : Good (rowAt 502) := by
  rw [row_502]
  unfold Good
  decide +kernel

def data_503 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2)}, {(-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -1), (7, 0), (7, 1), (7, 2)}, 14⟩
theorem entry_503_checked : entryAt 503 = entry_503 := by
  rw [entry_chunk_24 17 (by decide)]
  decide +kernel
theorem row_503 : rowAt 503 = data_503 := by
  rw [rowAt, dif_neg (by decide : ¬ 503 < 6), entry_503_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨55, 7, 4, 0⟩ (rowAt 55), placeRow ⟨420, 1, 7, 2⟩ (rowAt 420), placeRow ⟨419, 1, 7, 4⟩ (rowAt 419)] = data_503
  rw [row_63, row_55, row_420, row_419]
  apply row_ext <;> decide +kernel
theorem entry_good_503 : EntryGood 503 := by
  unfold EntryGood
  rw [entry_503_checked]
  decide +kernel
theorem good_503 : Good (rowAt 503) := by
  rw [row_503]
  unfold Good
  decide +kernel

def data_504 : RowData := ⟨{(1, -2), (1, -1), (1, 0), (1, 1)}, {(-4, -1), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)}, 13⟩
theorem entry_504_checked : entryAt 504 = entry_504 := by
  rw [entry_chunk_24 18 (by decide)]
  decide +kernel
theorem row_504 : rowAt 504 = data_504 := by
  rw [rowAt, dif_neg (by decide : ¬ 504 < 6), entry_504_checked]
  change forkRow [placeRow ⟨381, 0, 3, 4⟩ (rowAt 381), placeRow ⟨310, 4, 4, 5⟩ (rowAt 310), placeRow ⟨159, 0, 5, 6⟩ (rowAt 159), placeRow ⟨351, 4, 3, 4⟩ (rowAt 351), placeRow ⟨496, 0, 3, 4⟩ (rowAt 496)] = data_504
  rw [row_381, row_310, row_159, row_351, row_496]
  apply row_ext <;> decide +kernel
theorem entry_good_504 : EntryGood 504 := by
  unfold EntryGood
  rw [entry_504_checked]
  decide +kernel
theorem good_504 : Good (rowAt 504) := by
  rw [row_504]
  unfold Good
  decide +kernel

def data_505 : RowData := ⟨{(0, -2), (0, -1)}, {(-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, 1)}, 11⟩
theorem entry_505_checked : entryAt 505 = entry_505 := by
  rw [entry_chunk_24 19 (by decide)]
  decide +kernel
theorem row_505 : rowAt 505 = data_505 := by
  rw [rowAt, dif_neg (by decide : ¬ 505 < 6), entry_505_checked]
  change forkRow [placeRow ⟨173, 1, 4, 5⟩ (rowAt 173), placeRow ⟨499, 0, 5, 4⟩ (rowAt 499), placeRow ⟨183, 1, 4, 5⟩ (rowAt 183), placeRow ⟨282, 1, 4, 5⟩ (rowAt 282)] = data_505
  rw [row_173, row_499, row_183, row_282]
  apply row_ext <;> decide +kernel
theorem entry_good_505 : EntryGood 505 := by
  unfold EntryGood
  rw [entry_505_checked]
  decide +kernel
theorem good_505 : Good (rowAt 505) := by
  rw [row_505]
  unfold Good
  decide +kernel

def data_506 : RowData := ⟨{(-2, -2), (-2, 0), (-1, -3), (-1, -2), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 1), (4, -2)}, 11⟩
theorem entry_506_checked : entryAt 506 = entry_506 := by
  rw [entry_chunk_25 0 (by decide)]
  decide +kernel
theorem row_506 : rowAt 506 = data_506 := by
  rw [rowAt, dif_neg (by decide : ¬ 506 < 6), entry_506_checked]
  change forkRow [placeRow ⟨99, 0, 4, 5⟩ (rowAt 99), placeRow ⟨200, 7, 1, 4⟩ (rowAt 200), placeRow ⟨318, 5, 5, 4⟩ (rowAt 318), placeRow ⟨173, 0, 5, 4⟩ (rowAt 173)] = data_506
  rw [row_99, row_200, row_318, row_173]
  apply row_ext <;> decide +kernel
theorem entry_good_506 : EntryGood 506 := by
  unfold EntryGood
  rw [entry_506_checked]
  decide +kernel
theorem good_506 : Good (rowAt 506) := by
  rw [row_506]
  unfold Good
  decide +kernel

def data_507 : RowData := ⟨{(-2, -3), (-2, -2), (-1, 0), (-1, 1), (0, -2)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (5, 2)}, 12⟩
theorem entry_507_checked : entryAt 507 = entry_507 := by
  rw [entry_chunk_25 1 (by decide)]
  decide +kernel
theorem row_507 : rowAt 507 = data_507 := by
  rw [rowAt, dif_neg (by decide : ¬ 507 < 6), entry_507_checked]
  change forkRow [placeRow ⟨151, 0, 2, 4⟩ (rowAt 151), placeRow ⟨33, 3, 4, 3⟩ (rowAt 33), placeRow ⟨481, 0, 5, 4⟩ (rowAt 481)] = data_507
  rw [row_151, row_33, row_481]
  apply row_ext <;> decide +kernel
theorem entry_good_507 : EntryGood 507 := by
  unfold EntryGood
  rw [entry_507_checked]
  decide +kernel
theorem good_507 : Good (rowAt 507) := by
  rw [row_507]
  unfold Good
  decide +kernel

def data_508 : RowData := ⟨{(-3, -1), (-3, 0), (-2, -1), (-1, -2), (-1, -1), (0, -1)}, {(-5, 2), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2)}, 13⟩
theorem entry_508_checked : entryAt 508 = entry_508 := by
  rw [entry_chunk_25 2 (by decide)]
  decide +kernel
theorem row_508 : rowAt 508 = data_508 := by
  rw [rowAt, dif_neg (by decide : ¬ 508 < 6), entry_508_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨393, 0, 1, 5⟩ (rowAt 393)] = data_508
  rw [row_6, row_393]
  apply row_ext <;> decide +kernel
theorem entry_good_508 : EntryGood 508 := by
  unfold EntryGood
  rw [entry_508_checked]
  decide +kernel
theorem good_508 : Good (rowAt 508) := by
  rw [row_508]
  unfold Good
  decide +kernel

def data_509 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0), (1, 0)}, {(-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 8⟩
theorem entry_509_checked : entryAt 509 = entry_509 := by
  rw [entry_chunk_25 3 (by decide)]
  decide +kernel
theorem row_509 : rowAt 509 = data_509 := by
  rw [rowAt, dif_neg (by decide : ¬ 509 < 6), entry_509_checked]
  change forkRow [placeRow ⟨252, 0, 6, 4⟩ (rowAt 252), placeRow ⟨241, 4, 2, 4⟩ (rowAt 241), placeRow ⟨455, 0, 6, 3⟩ (rowAt 455), placeRow ⟨68, 2, 6, 4⟩ (rowAt 68)] = data_509
  rw [row_252, row_241, row_455, row_68]
  apply row_ext <;> decide +kernel
theorem entry_good_509 : EntryGood 509 := by
  unfold EntryGood
  rw [entry_509_checked]
  decide +kernel
theorem good_509 : Good (rowAt 509) := by
  rw [row_509]
  unfold Good
  decide +kernel

def data_510 : RowData := ⟨{(0, -1), (1, -1), (2, -2), (2, -1), (3, -1)}, {(-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2)}, 14⟩
theorem entry_510_checked : entryAt 510 = entry_510 := by
  rw [entry_chunk_25 4 (by decide)]
  decide +kernel
theorem row_510 : rowAt 510 = data_510 := by
  rw [rowAt, dif_neg (by decide : ¬ 510 < 6), entry_510_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨508, 0, 7, 4⟩ (rowAt 508)] = data_510
  rw [row_6, row_508]
  apply row_ext <;> decide +kernel
theorem entry_good_510 : EntryGood 510 := by
  unfold EntryGood
  rw [entry_510_checked]
  decide +kernel
theorem good_510 : Good (rowAt 510) := by
  rw [row_510]
  unfold Good
  decide +kernel

def data_511 : RowData := ⟨{(-3, -2), (-2, -2), (-1, -2), (-1, -1), (-1, 0), (0, 2)}, {(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 10⟩
theorem entry_511_checked : entryAt 511 = entry_511 := by
  rw [entry_chunk_25 5 (by decide)]
  decide +kernel
theorem row_511 : rowAt 511 = data_511 := by
  rw [rowAt, dif_neg (by decide : ¬ 511 < 6), entry_511_checked]
  change forkRow [placeRow ⟨15, 1, 4, 5⟩ (rowAt 15), placeRow ⟨331, 0, 5, 3⟩ (rowAt 331), placeRow ⟨380, 4, 2, 4⟩ (rowAt 380)] = data_511
  rw [row_15, row_331, row_380]
  apply row_ext <;> decide +kernel
theorem entry_good_511 : EntryGood 511 := by
  unfold EntryGood
  rw [entry_511_checked]
  decide +kernel
theorem good_511 : Good (rowAt 511) := by
  rw [row_511]
  unfold Good
  decide +kernel

#check row_511
def data_512 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0), (-1, 2), (-1, 3)}, {(-4, 2), (-3, -1), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 3), (4, 4), (5, 4)}, 13⟩
theorem entry_512_checked : entryAt 512 = entry_512 := by
  rw [entry_chunk_25 6 (by decide)]
  decide +kernel
theorem row_512 : rowAt 512 = data_512 := by
  rw [rowAt, dif_neg (by decide : ¬ 512 < 6), entry_512_checked]
  change forkRow [placeRow ⟨62, 0, 5, 4⟩ (rowAt 62), placeRow ⟨107, 0, 5, 4⟩ (rowAt 107), placeRow ⟨507, 0, 4, 6⟩ (rowAt 507)] = data_512
  rw [row_62, row_107, row_507]
  apply row_ext <;> decide +kernel
theorem entry_good_512 : EntryGood 512 := by
  unfold EntryGood
  rw [entry_512_checked]
  decide +kernel
theorem good_512 : Good (rowAt 512) := by
  rw [row_512]
  unfold Good
  decide +kernel

def data_513 : RowData := ⟨{(0, -1), (1, -1), (2, -1), (3, -1)}, {(-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2)}, 14⟩
theorem entry_513_checked : entryAt 513 = entry_513 := by
  rw [entry_chunk_25 7 (by decide)]
  decide +kernel
theorem row_513 : rowAt 513 = data_513 := by
  rw [rowAt, dif_neg (by decide : ¬ 513 < 6), entry_513_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨396, 0, 4, 5⟩ (rowAt 396)] = data_513
  rw [row_6, row_396]
  apply row_ext <;> decide +kernel
theorem entry_good_513 : EntryGood 513 := by
  unfold EntryGood
  rw [entry_513_checked]
  decide +kernel
theorem good_513 : Good (rowAt 513) := by
  rw [row_513]
  unfold Good
  decide +kernel

def data_514 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0)}, {(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)}, 21⟩
theorem entry_514_checked : entryAt 514 = entry_514 := by
  rw [entry_chunk_25 8 (by decide)]
  decide +kernel
theorem row_514 : rowAt 514 = data_514 := by
  rw [rowAt, dif_neg (by decide : ¬ 514 < 6), entry_514_checked]
  change forkRow [placeRow ⟨57, 0, 5, 4⟩ (rowAt 57), placeRow ⟨443, 4, 1, 5⟩ (rowAt 443), placeRow ⟨510, 0, 1, 5⟩ (rowAt 510)] = data_514
  rw [row_57, row_443, row_510]
  apply row_ext <;> decide +kernel
theorem entry_good_514 : EntryGood 514 := by
  unfold EntryGood
  rw [entry_514_checked]
  decide +kernel
theorem good_514 : Good (rowAt 514) := by
  rw [row_514]
  unfold Good
  decide +kernel

def data_515 : RowData := ⟨{(-4, -1), (-3, -1), (-3, 0), (-1, 0)}, {(-4, -2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4)}, 14⟩
theorem entry_515_checked : entryAt 515 = entry_515 := by
  rw [entry_chunk_25 9 (by decide)]
  decide +kernel
theorem row_515 : rowAt 515 = data_515 := by
  rw [rowAt, dif_neg (by decide : ¬ 515 < 6), entry_515_checked]
  change forkRow [placeRow ⟨2, 6, 2, 4⟩ (rowAt 2), placeRow ⟨512, 1, 1, 5⟩ (rowAt 512)] = data_515
  rw [row_2, row_512]
  apply row_ext <;> decide +kernel
theorem entry_good_515 : EntryGood 515 := by
  unfold EntryGood
  rw [entry_515_checked]
  decide +kernel
theorem good_515 : Good (rowAt 515) := by
  rw [row_515]
  unfold Good
  decide +kernel

def data_516 : RowData := ⟨{(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2)}, {(-6, -2), (-5, -2), (-5, -1), (-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 12⟩
theorem entry_516_checked : entryAt 516 = entry_516 := by
  rw [entry_chunk_25 10 (by decide)]
  decide +kernel
theorem row_516 : rowAt 516 = data_516 := by
  rw [rowAt, dif_neg (by decide : ¬ 516 < 6), entry_516_checked]
  change forkRow [placeRow ⟨329, 0, 4, 3⟩ (rowAt 329), placeRow ⟨244, 4, 2, 4⟩ (rowAt 244), placeRow ⟨10, 1, 4, 5⟩ (rowAt 10), placeRow ⟨506, 4, 2, 4⟩ (rowAt 506)] = data_516
  rw [row_329, row_244, row_10, row_506]
  apply row_ext <;> decide +kernel
theorem entry_good_516 : EntryGood 516 := by
  unfold EntryGood
  rw [entry_516_checked]
  decide +kernel
theorem good_516 : Good (rowAt 516) := by
  rw [row_516]
  unfold Good
  decide +kernel

def data_517 : RowData := ⟨{(-1, -3), (-1, -1), (0, -3), (0, -1)}, {(-5, -2), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, 0)}, 13⟩
theorem entry_517_checked : entryAt 517 = entry_517 := by
  rw [entry_chunk_25 11 (by decide)]
  decide +kernel
theorem row_517 : rowAt 517 = data_517 := by
  rw [rowAt, dif_neg (by decide : ¬ 517 < 6), entry_517_checked]
  change forkRow [placeRow ⟨496, 0, 2, 3⟩ (rowAt 496), placeRow ⟨140, 0, 4, 2⟩ (rowAt 140), placeRow ⟨193, 1, 4, 2⟩ (rowAt 193)] = data_517
  rw [row_496, row_140, row_193]
  apply row_ext <;> decide +kernel
theorem entry_good_517 : EntryGood 517 := by
  unfold EntryGood
  rw [entry_517_checked]
  decide +kernel
theorem good_517 : Good (rowAt 517) := by
  rw [row_517]
  unfold Good
  decide +kernel

def data_518 : RowData := ⟨{(1, -1), (1, 0), (2, -1), (2, 0)}, {(-5, 2), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1), (6, 2), (6, 3)}, 22⟩
theorem entry_518_checked : entryAt 518 = entry_518 := by
  rw [entry_chunk_25 12 (by decide)]
  decide +kernel
theorem row_518 : rowAt 518 = data_518 := by
  rw [rowAt, dif_neg (by decide : ¬ 518 < 6), entry_518_checked]
  change forkRow [placeRow ⟨9, 6, 3, 4⟩ (rowAt 9), placeRow ⟨514, 0, 7, 4⟩ (rowAt 514)] = data_518
  rw [row_9, row_514]
  apply row_ext <;> decide +kernel
theorem entry_good_518 : EntryGood 518 := by
  unfold EntryGood
  rw [entry_518_checked]
  decide +kernel
theorem good_518 : Good (rowAt 518) := by
  rw [row_518]
  unfold Good
  decide +kernel

def data_519 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, -1)}, {(-6, -1), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (5, 0)}, 12⟩
theorem entry_519_checked : entryAt 519 = entry_519 := by
  rw [entry_chunk_25 13 (by decide)]
  decide +kernel
theorem row_519 : rowAt 519 = data_519 := by
  rw [rowAt, dif_neg (by decide : ¬ 519 < 6), entry_519_checked]
  change forkRow [placeRow ⟨498, 0, 4, 3⟩ (rowAt 498), placeRow ⟨311, 4, 3, 4⟩ (rowAt 311), placeRow ⟨38, 1, 4, 5⟩ (rowAt 38), placeRow ⟨408, 0, 3, 4⟩ (rowAt 408)] = data_519
  rw [row_498, row_311, row_38, row_408]
  apply row_ext <;> decide +kernel
theorem entry_good_519 : EntryGood 519 := by
  unfold EntryGood
  rw [entry_519_checked]
  decide +kernel
theorem good_519 : Good (rowAt 519) := by
  rw [row_519]
  unfold Good
  decide +kernel

def data_520 : RowData := ⟨{(-2, -3), (-1, 0), (1, -2), (1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -5), (0, -4), (0, -3), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -5), (2, -4), (2, -3), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 8⟩
theorem entry_520_checked : entryAt 520 = entry_520 := by
  rw [entry_chunk_25 14 (by decide)]
  decide +kernel
theorem row_520 : rowAt 520 = data_520 := by
  rw [rowAt, dif_neg (by decide : ¬ 520 < 6), entry_520_checked]
  change forkRow [placeRow ⟨254, 0, 2, 3⟩ (rowAt 254), placeRow ⟨200, 5, 6, 4⟩ (rowAt 200), placeRow ⟨271, 6, 5, 3⟩ (rowAt 271), placeRow ⟨215, 2, 5, 3⟩ (rowAt 215), placeRow ⟨252, 4, 2, 4⟩ (rowAt 252)] = data_520
  rw [row_254, row_200, row_271, row_215, row_252]
  apply row_ext <;> decide +kernel
theorem entry_good_520 : EntryGood 520 := by
  unfold EntryGood
  rw [entry_520_checked]
  decide +kernel
theorem good_520 : Good (rowAt 520) := by
  rw [row_520]
  unfold Good
  decide +kernel

def data_521 : RowData := ⟨{(-1, -4), (-1, -3), (0, -3), (0, -1)}, {(-6, 1), (-5, -2), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2), (2, -1), (3, -4), (3, -3), (3, -2), (3, -1), (4, -4), (4, -2)}, 14⟩
theorem entry_521_checked : entryAt 521 = entry_521 := by
  rw [entry_chunk_25 15 (by decide)]
  decide +kernel
theorem row_521 : rowAt 521 = data_521 := by
  rw [rowAt, dif_neg (by decide : ¬ 521 < 6), entry_521_checked]
  change forkRow [placeRow ⟨492, 4, 5, 1⟩ (rowAt 492), placeRow ⟨2, 7, 4, 2⟩ (rowAt 2)] = data_521
  rw [row_492, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_521 : EntryGood 521 := by
  unfold EntryGood
  rw [entry_521_checked]
  decide +kernel
theorem good_521 : Good (rowAt 521) := by
  rw [row_521]
  unfold Good
  decide +kernel

def data_522 : RowData := ⟨{(-2, -1), (0, -1), (0, 1)}, {(-5, -2), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 2), (3, -2), (3, -1), (3, 0), (3, 2), (4, -2), (4, -1), (4, 0), (5, -2)}, 9⟩
theorem entry_522_checked : entryAt 522 = entry_522 := by
  rw [entry_chunk_25 16 (by decide)]
  decide +kernel
theorem row_522 : rowAt 522 = data_522 := by
  rw [rowAt, dif_neg (by decide : ¬ 522 < 6), entry_522_checked]
  change forkRow [placeRow ⟨176, 3, 4, 6⟩ (rowAt 176), placeRow ⟨338, 2, 3, 3⟩ (rowAt 338), placeRow ⟨252, 1, 4, 6⟩ (rowAt 252)] = data_522
  rw [row_176, row_338, row_252]
  apply row_ext <;> decide +kernel
theorem entry_good_522 : EntryGood 522 := by
  unfold EntryGood
  rw [entry_522_checked]
  decide +kernel
theorem good_522 : Good (rowAt 522) := by
  rw [row_522]
  unfold Good
  decide +kernel

def data_523 : RowData := ⟨{(-3, 4), (-2, 0), (-2, 1), (-2, 2), (-1, 0)}, {(-7, 1), (-7, 3), (-6, 1), (-6, 2), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 5), (-4, 6), (-4, 7), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (4, 2)}, 11⟩
theorem entry_523_checked : entryAt 523 = entry_523 := by
  rw [entry_chunk_25 17 (by decide)]
  decide +kernel
theorem row_523 : rowAt 523 = data_523 := by
  rw [rowAt, dif_neg (by decide : ¬ 523 < 6), entry_523_checked]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (rowAt 303), placeRow ⟨25, 4, 1, 5⟩ (rowAt 25), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107), placeRow ⟨511, 4, 1, 6⟩ (rowAt 511)] = data_523
  rw [row_303, row_25, row_107, row_511]
  apply row_ext <;> decide +kernel
theorem entry_good_523 : EntryGood 523 := by
  unfold EntryGood
  rw [entry_523_checked]
  decide +kernel
theorem good_523 : Good (rowAt 523) := by
  rw [row_523]
  unfold Good
  decide +kernel

def data_524 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-5, -2), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, 0), (5, 1)}, 14⟩
theorem entry_524_checked : entryAt 524 = entry_524 := by
  rw [entry_chunk_25 18 (by decide)]
  decide +kernel
theorem row_524 : rowAt 524 = data_524 := by
  rw [rowAt, dif_neg (by decide : ¬ 524 < 6), entry_524_checked]
  change forkRow [placeRow ⟨504, 4, 5, 3⟩ (rowAt 504), placeRow ⟨504, 0, 3, 3⟩ (rowAt 504), placeRow ⟨180, 0, 4, 5⟩ (rowAt 180), placeRow ⟨180, 4, 4, 5⟩ (rowAt 180), placeRow ⟨261, 0, 3, 4⟩ (rowAt 261)] = data_524
  rw [row_504, row_180, row_261]
  apply row_ext <;> decide +kernel
theorem entry_good_524 : EntryGood 524 := by
  unfold EntryGood
  rw [entry_524_checked]
  decide +kernel
theorem good_524 : Good (rowAt 524) := by
  rw [row_524]
  unfold Good
  decide +kernel

def data_525 : RowData := ⟨{(-2, 0), (-2, 1), (-2, 2), (-1, 0)}, {(-7, 1), (-7, 3), (-6, 1), (-6, 2), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3), (5, 1)}, 11⟩
theorem entry_525_checked : entryAt 525 = entry_525 := by
  rw [entry_chunk_25 19 (by decide)]
  decide +kernel
theorem row_525 : rowAt 525 = data_525 := by
  rw [rowAt, dif_neg (by decide : ¬ 525 < 6), entry_525_checked]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (rowAt 303), placeRow ⟨25, 4, 1, 5⟩ (rowAt 25), placeRow ⟨430, 0, 4, 6⟩ (rowAt 430), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107)] = data_525
  rw [row_303, row_25, row_430, row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_525 : EntryGood 525 := by
  unfold EntryGood
  rw [entry_525_checked]
  decide +kernel
theorem good_525 : Good (rowAt 525) := by
  rw [row_525]
  unfold Good
  decide +kernel

def data_526 : RowData := ⟨{(-1, -2), (-1, 0), (0, -2)}, {(-6, 1), (-6, 2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 17⟩
theorem entry_526_checked : entryAt 526 = entry_526 := by
  rw [entry_chunk_26 0 (by decide)]
  decide +kernel
theorem row_526 : rowAt 526 = data_526 := by
  rw [rowAt, dif_neg (by decide : ¬ 526 < 6), entry_526_checked]
  change forkRow [placeRow ⟨359, 0, 4, 3⟩ (rowAt 359), placeRow ⟨416, 4, 2, 4⟩ (rowAt 416), placeRow ⟨327, 5, 4, 3⟩ (rowAt 327), placeRow ⟨489, 0, 5, 4⟩ (rowAt 489), placeRow ⟨399, 3, 2, 4⟩ (rowAt 399)] = data_526
  rw [row_359, row_416, row_327, row_489, row_399]
  apply row_ext <;> decide +kernel
theorem entry_good_526 : EntryGood 526 := by
  unfold EntryGood
  rw [entry_526_checked]
  decide +kernel
theorem good_526 : Good (rowAt 526) := by
  rw [row_526]
  unfold Good
  decide +kernel

def data_527 : RowData := ⟨{(1, -3), (1, -2), (1, -1)}, {(-5, 1), (-4, -2), (-4, -1), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (7, 0)}, 13⟩
theorem entry_527_checked : entryAt 527 = entry_527 := by
  rw [entry_chunk_26 1 (by decide)]
  decide +kernel
theorem row_527 : rowAt 527 = data_527 := by
  rw [rowAt, dif_neg (by decide : ¬ 527 < 6), entry_527_checked]
  change forkRow [placeRow ⟨387, 4, 4, 3⟩ (rowAt 387), placeRow ⟨38, 3, 4, 5⟩ (rowAt 38), placeRow ⟨491, 0, 5, 4⟩ (rowAt 491), placeRow ⟨519, 0, 6, 4⟩ (rowAt 519)] = data_527
  rw [row_387, row_38, row_491, row_519]
  apply row_ext <;> decide +kernel
theorem entry_good_527 : EntryGood 527 := by
  unfold EntryGood
  rw [entry_527_checked]
  decide +kernel
theorem good_527 : Good (rowAt 527) := by
  rw [row_527]
  unfold Good
  decide +kernel

def data_528 : RowData := ⟨{(-2, -1), (-2, 0), (-2, 1), (0, 1)}, {(-7, 0), (-7, 2), (-6, 0), (-6, 1), (-6, 2), (-5, 0), (-5, 1), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 3)}, 12⟩
theorem entry_528_checked : entryAt 528 = entry_528 := by
  rw [entry_chunk_26 2 (by decide)]
  decide +kernel
theorem row_528 : rowAt 528 = data_528 := by
  rw [rowAt, dif_neg (by decide : ¬ 528 < 6), entry_528_checked]
  change forkRow [placeRow ⟨414, 1, 3, 5⟩ (rowAt 414), placeRow ⟨386, 1, 4, 6⟩ (rowAt 386), placeRow ⟨502, 5, 4, 3⟩ (rowAt 502), placeRow ⟨226, 4, 1, 5⟩ (rowAt 226), placeRow ⟨359, 5, 3, 4⟩ (rowAt 359)] = data_528
  rw [row_414, row_386, row_502, row_226, row_359]
  apply row_ext <;> decide +kernel
theorem entry_good_528 : EntryGood 528 := by
  unfold EntryGood
  rw [entry_528_checked]
  decide +kernel
theorem good_528 : Good (rowAt 528) := by
  rw [row_528]
  unfold Good
  decide +kernel

def data_529 : RowData := ⟨{(1, 0), (2, 0), (3, 0)}, {(-2, -1), (-2, 1), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)}, 16⟩
theorem entry_529_checked : entryAt 529 = entry_529 := by
  rw [entry_chunk_26 3 (by decide)]
  decide +kernel
theorem row_529 : rowAt 529 = data_529 := by
  rw [rowAt, dif_neg (by decide : ¬ 529 < 6), entry_529_checked]
  change forkRow [placeRow ⟨55, 4, 3, 4⟩ (rowAt 55), placeRow ⟨441, 0, 4, 3⟩ (rowAt 441), placeRow ⟨63, 3, 3, 3⟩ (rowAt 63), placeRow ⟨64, 6, 7, 5⟩ (rowAt 64)] = data_529
  rw [row_55, row_441, row_63, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_529 : EntryGood 529 := by
  unfold EntryGood
  rw [entry_529_checked]
  decide +kernel
theorem good_529 : Good (rowAt 529) := by
  rw [row_529]
  unfold Good
  decide +kernel

def data_530 : RowData := ⟨{(0, -1), (0, 1), (2, -1), (2, 1)}, {(-4, -3), (-4, -1), (-4, 0), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)}, 13⟩
theorem entry_530_checked : entryAt 530 = entry_530 := by
  rw [entry_chunk_26 4 (by decide)]
  decide +kernel
theorem row_530 : rowAt 530 = data_530 := by
  rw [rowAt, dif_neg (by decide : ¬ 530 < 6), entry_530_checked]
  change forkRow [placeRow ⟨456, 7, 4, 2⟩ (rowAt 456), placeRow ⟨336, 0, 5, 5⟩ (rowAt 336), placeRow ⟨283, 7, 4, 2⟩ (rowAt 283), placeRow ⟨271, 5, 5, 5⟩ (rowAt 271)] = data_530
  rw [row_456, row_336, row_283, row_271]
  apply row_ext <;> decide +kernel
theorem entry_good_530 : EntryGood 530 := by
  unfold EntryGood
  rw [entry_530_checked]
  decide +kernel
theorem good_530 : Good (rowAt 530) := by
  rw [row_530]
  unfold Good
  decide +kernel

def data_531 : RowData := ⟨{(0, -2), (1, -2)}, {(-5, -1), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1)}, 18⟩
theorem entry_531_checked : entryAt 531 = entry_531 := by
  rw [entry_chunk_26 5 (by decide)]
  decide +kernel
theorem row_531 : rowAt 531 = data_531 := by
  rw [rowAt, dif_neg (by decide : ¬ 531 < 6), entry_531_checked]
  change forkRow [placeRow ⟨425, 0, 5, 4⟩ (rowAt 425), placeRow ⟨336, 3, 4, 3⟩ (rowAt 336), placeRow ⟨340, 6, 4, 3⟩ (rowAt 340), placeRow ⟨394, 1, 5, 4⟩ (rowAt 394), placeRow ⟨423, 0, 5, 4⟩ (rowAt 423), placeRow ⟨526, 0, 5, 4⟩ (rowAt 526), placeRow ⟨401, 4, 4, 3⟩ (rowAt 401), placeRow ⟨453, 0, 5, 4⟩ (rowAt 453)] = data_531
  rw [row_425, row_336, row_340, row_394, row_423, row_526, row_401, row_453]
  apply row_ext <;> decide +kernel
theorem entry_good_531 : EntryGood 531 := by
  unfold EntryGood
  rw [entry_531_checked]
  decide +kernel
theorem good_531 : Good (rowAt 531) := by
  rw [row_531]
  unfold Good
  decide +kernel

def data_532 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (0, -1)}, {(-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, 0), (5, 1)}, 14⟩
theorem entry_532_checked : entryAt 532 = entry_532 := by
  rw [entry_chunk_26 6 (by decide)]
  decide +kernel
theorem row_532 : rowAt 532 = data_532 := by
  rw [rowAt, dif_neg (by decide : ¬ 532 < 6), entry_532_checked]
  change forkRow [placeRow ⟨504, 4, 5, 3⟩ (rowAt 504), placeRow ⟨6, 7, 3, 0⟩ (rowAt 6)] = data_532
  rw [row_504, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_532 : EntryGood 532 := by
  unfold EntryGood
  rw [entry_532_checked]
  decide +kernel
theorem good_532 : Good (rowAt 532) := by
  rw [row_532]
  unfold Good
  decide +kernel

def data_533 : RowData := ⟨{(0, -2), (0, -1)}, {(-5, -1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (2, -4), (2, -3), (2, -2), (2, 0), (2, 1), (3, -4), (3, -3), (3, -2), (3, 0), (4, -4), (4, -3), (4, -2), (5, -2)}, 11⟩
theorem entry_533_checked : entryAt 533 = entry_533 := by
  rw [entry_chunk_26 7 (by decide)]
  decide +kernel
theorem row_533 : rowAt 533 = data_533 := by
  rw [rowAt, dif_neg (by decide : ¬ 533 < 6), entry_533_checked]
  change forkRow [placeRow ⟨318, 4, 4, 5⟩ (rowAt 318), placeRow ⟨319, 7, 5, 1⟩ (rowAt 319), placeRow ⟨407, 4, 4, 1⟩ (rowAt 407), placeRow ⟨173, 3, 4, 5⟩ (rowAt 173), placeRow ⟨217, 1, 4, 5⟩ (rowAt 217)] = data_533
  rw [row_318, row_319, row_407, row_173, row_217]
  apply row_ext <;> decide +kernel
theorem entry_good_533 : EntryGood 533 := by
  unfold EntryGood
  rw [entry_533_checked]
  decide +kernel
theorem good_533 : Good (rowAt 533) := by
  rw [row_533]
  unfold Good
  decide +kernel

def data_534 : RowData := ⟨{(-2, -1), (-2, 0), (-2, 2), (-1, -1), (-1, 0), (-1, 2)}, {(-5, 3), (-5, 5), (-4, -1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)}, 16⟩
theorem entry_534_checked : entryAt 534 = entry_534 := by
  rw [entry_chunk_26 8 (by decide)]
  decide +kernel
theorem row_534 : rowAt 534 = data_534 := by
  rw [rowAt, dif_neg (by decide : ¬ 534 < 6), entry_534_checked]
  change forkRow [placeRow ⟨434, 0, 4, 6⟩ (rowAt 434), placeRow ⟨12, 6, 1, 3⟩ (rowAt 12)] = data_534
  rw [row_434, row_12]
  apply row_ext <;> decide +kernel
theorem entry_good_534 : EntryGood 534 := by
  unfold EntryGood
  rw [entry_534_checked]
  decide +kernel
theorem good_534 : Good (rowAt 534) := by
  rw [row_534]
  unfold Good
  decide +kernel

def data_535 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1)}, {(-5, -2), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3)}, 15⟩
theorem entry_535_checked : entryAt 535 = entry_535 := by
  rw [entry_chunk_26 9 (by decide)]
  decide +kernel
theorem row_535 : rowAt 535 = data_535 := by
  rw [rowAt, dif_neg (by decide : ¬ 535 < 6), entry_535_checked]
  change forkRow [placeRow ⟨444, 0, 4, 5⟩ (rowAt 444), placeRow ⟨426, 0, 4, 5⟩ (rowAt 426), placeRow ⟨25, 0, 5, 4⟩ (rowAt 25), placeRow ⟨321, 4, 4, 2⟩ (rowAt 321)] = data_535
  rw [row_444, row_426, row_25, row_321]
  apply row_ext <;> decide +kernel
theorem entry_good_535 : EntryGood 535 := by
  unfold EntryGood
  rw [entry_535_checked]
  decide +kernel
theorem good_535 : Good (rowAt 535) := by
  rw [row_535]
  unfold Good
  decide +kernel

def data_536 : RowData := ⟨{(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2)}, {(-4, 1), (-4, 3), (-3, -3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1)}, 17⟩
theorem entry_536_checked : entryAt 536 = entry_536 := by
  rw [entry_chunk_26 10 (by decide)]
  decide +kernel
theorem row_536 : rowAt 536 = data_536 := by
  rw [rowAt, dif_neg (by decide : ¬ 536 < 6), entry_536_checked]
  change forkRow [placeRow ⟨307, 0, 4, 3⟩ (rowAt 307), placeRow ⟨244, 0, 5, 4⟩ (rowAt 244), placeRow ⟨26, 3, 4, 3⟩ (rowAt 26), placeRow ⟨534, 0, 5, 2⟩ (rowAt 534)] = data_536
  rw [row_307, row_244, row_26, row_534]
  apply row_ext <;> decide +kernel
theorem entry_good_536 : EntryGood 536 := by
  unfold EntryGood
  rw [entry_536_checked]
  decide +kernel
theorem good_536 : Good (rowAt 536) := by
  rw [row_536]
  unfold Good
  decide +kernel

def data_537 : RowData := ⟨{(-3, 1), (-2, -1), (-2, 1), (0, -1), (0, 1)}, {(-7, -2), (-7, 0), (-6, -2), (-6, -1), (-6, 0), (-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0)}, 11⟩
theorem entry_537_checked : entryAt 537 = entry_537 := by
  rw [entry_chunk_26 11 (by decide)]
  decide +kernel
theorem row_537 : rowAt 537 = data_537 := by
  rw [rowAt, dif_neg (by decide : ¬ 537 < 6), entry_537_checked]
  change forkRow [placeRow ⟨373, 2, 2, 4⟩ (rowAt 373), placeRow ⟨271, 3, 3, 3⟩ (rowAt 271), placeRow ⟨176, 1, 4, 6⟩ (rowAt 176), placeRow ⟨330, 1, 4, 6⟩ (rowAt 330)] = data_537
  rw [row_373, row_271, row_176, row_330]
  apply row_ext <;> decide +kernel
theorem entry_good_537 : EntryGood 537 := by
  unfold EntryGood
  rw [entry_537_checked]
  decide +kernel
theorem good_537 : Good (rowAt 537) := by
  rw [row_537]
  unfold Good
  decide +kernel

def data_538 : RowData := ⟨{(1, 0), (2, 0), (3, 0)}, {(-2, -1), (-2, 1), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 5), (7, 6), (7, 7)}, 22⟩
theorem entry_538_checked : entryAt 538 = entry_538 := by
  rw [entry_chunk_26 12 (by decide)]
  decide +kernel
theorem row_538 : rowAt 538 = data_538 := by
  rw [rowAt, dif_neg (by decide : ¬ 538 < 6), entry_538_checked]
  change forkRow [placeRow ⟨63, 3, 3, 3⟩ (rowAt 63), placeRow ⟨470, 0, 4, 5⟩ (rowAt 470), placeRow ⟨64, 6, 7, 5⟩ (rowAt 64), placeRow ⟨55, 4, 3, 4⟩ (rowAt 55)] = data_538
  rw [row_63, row_470, row_64, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_538 : EntryGood 538 := by
  unfold EntryGood
  rw [entry_538_checked]
  decide +kernel
theorem good_538 : Good (rowAt 538) := by
  rw [row_538]
  unfold Good
  decide +kernel

def data_539 : RowData := ⟨{(0, -3), (0, -2), (1, -3), (1, -2)}, {(-5, -2), (-4, -4), (-4, -2), (-4, -1), (-4, 1), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 1)}, 18⟩
theorem entry_539_checked : entryAt 539 = entry_539 := by
  rw [entry_chunk_26 13 (by decide)]
  decide +kernel
theorem row_539 : rowAt 539 = data_539 := by
  rw [rowAt, dif_neg (by decide : ¬ 539 < 6), entry_539_checked]
  change forkRow [placeRow ⟨51, 1, 5, 4⟩ (rowAt 51), placeRow ⟨488, 3, 4, 3⟩ (rowAt 488), placeRow ⟨428, 0, 5, 4⟩ (rowAt 428), placeRow ⟨516, 0, 5, 4⟩ (rowAt 516)] = data_539
  rw [row_51, row_488, row_428, row_516]
  apply row_ext <;> decide +kernel
theorem entry_good_539 : EntryGood 539 := by
  unfold EntryGood
  rw [entry_539_checked]
  decide +kernel
theorem good_539 : Good (rowAt 539) := by
  rw [row_539]
  unfold Good
  decide +kernel

def data_540 : RowData := ⟨{(0, -3), (0, -2), (1, -3), (1, -2)}, {(-3, -3), (-3, 1), (-3, 3), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1)}, 18⟩
theorem entry_540_checked : entryAt 540 = entry_540 := by
  rw [entry_chunk_26 14 (by decide)]
  decide +kernel
theorem row_540 : rowAt 540 = data_540 := by
  rw [rowAt, dif_neg (by decide : ¬ 540 < 6), entry_540_checked]
  change forkRow [placeRow ⟨334, 0, 4, 3⟩ (rowAt 334), placeRow ⟨51, 1, 5, 4⟩ (rowAt 51), placeRow ⟨88, 3, 4, 3⟩ (rowAt 88), placeRow ⟨536, 0, 5, 4⟩ (rowAt 536)] = data_540
  rw [row_334, row_51, row_88, row_536]
  apply row_ext <;> decide +kernel
theorem entry_good_540 : EntryGood 540 := by
  unfold EntryGood
  rw [entry_540_checked]
  decide +kernel
theorem good_540 : Good (rowAt 540) := by
  rw [row_540]
  unfold Good
  decide +kernel

def data_541 : RowData := ⟨{(-2, -2), (-1, -2), (0, -2), (0, -1)}, {(-5, 0), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)}, 14⟩
theorem entry_541_checked : entryAt 541 = entry_541 := by
  rw [entry_chunk_26 15 (by decide)]
  decide +kernel
theorem row_541 : rowAt 541 = data_541 := by
  rw [rowAt, dif_neg (by decide : ¬ 541 < 6), entry_541_checked]
  change forkRow [placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨142, 7, 4, 1⟩ (rowAt 142), placeRow ⟨160, 3, 4, 1⟩ (rowAt 160), placeRow ⟨194, 0, 5, 3⟩ (rowAt 194), placeRow ⟨501, 4, 1, 2⟩ (rowAt 501), placeRow ⟨412, 0, 5, 3⟩ (rowAt 412)] = data_541
  rw [row_236, row_142, row_160, row_194, row_501, row_412]
  apply row_ext <;> decide +kernel
theorem entry_good_541 : EntryGood 541 := by
  unfold EntryGood
  rw [entry_541_checked]
  decide +kernel
theorem good_541 : Good (rowAt 541) := by
  rw [row_541]
  unfold Good
  decide +kernel

def data_542 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3)}, {(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)}, 17⟩
theorem entry_542_checked : entryAt 542 = entry_542 := by
  rw [entry_chunk_26 16 (by decide)]
  decide +kernel
theorem row_542 : rowAt 542 = data_542 := by
  rw [rowAt, dif_neg (by decide : ¬ 542 < 6), entry_542_checked]
  change forkRow [placeRow ⟨6, 5, 5, 0⟩ (rowAt 6), placeRow ⟨442, 0, 4, 5⟩ (rowAt 442)] = data_542
  rw [row_6, row_442]
  apply row_ext <;> decide +kernel
theorem entry_good_542 : EntryGood 542 := by
  unfold EntryGood
  rw [entry_542_checked]
  decide +kernel
theorem good_542 : Good (rowAt 542) := by
  rw [row_542]
  unfold Good
  decide +kernel

def data_543 : RowData := ⟨{(-2, 0), (-2, 1), (-1, 0)}, {(-6, 3), (-5, -1), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -2), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 1), (4, -2)}, 11⟩
theorem entry_543_checked : entryAt 543 = entry_543 := by
  rw [entry_chunk_26 17 (by decide)]
  decide +kernel
theorem row_543 : rowAt 543 = data_543 := by
  rw [rowAt, dif_neg (by decide : ¬ 543 < 6), entry_543_checked]
  change forkRow [placeRow ⟨493, 3, 2, 6⟩ (rowAt 493), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107), placeRow ⟨318, 5, 5, 4⟩ (rowAt 318)] = data_543
  rw [row_493, row_107, row_318]
  apply row_ext <;> decide +kernel
theorem entry_good_543 : EntryGood 543 := by
  unfold EntryGood
  rw [entry_543_checked]
  decide +kernel
theorem good_543 : Good (rowAt 543) := by
  rw [row_543]
  unfold Good
  decide +kernel

#check row_543
def data_544 : RowData := ⟨{(1, -1), (1, 0), (2, -1), (2, 0)}, {(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (10, -2), (10, 0), (10, 2)}, 18⟩
theorem entry_544_checked : entryAt 544 = entry_544 := by
  rw [entry_chunk_26 18 (by decide)]
  decide +kernel
theorem row_544 : rowAt 544 = data_544 := by
  rw [rowAt, dif_neg (by decide : ¬ 544 < 6), entry_544_checked]
  change forkRow [placeRow ⟨263, 2, 7, 4⟩ (rowAt 263), placeRow ⟨9, 6, 3, 4⟩ (rowAt 9), placeRow ⟨451, 1, 8, 3⟩ (rowAt 451)] = data_544
  rw [row_263, row_9, row_451]
  apply row_ext <;> decide +kernel
theorem entry_good_544 : EntryGood 544 := by
  unfold EntryGood
  rw [entry_544_checked]
  decide +kernel
theorem good_544 : Good (rowAt 544) := by
  rw [row_544]
  unfold Good
  decide +kernel

def data_545 : RowData := ⟨{(-1, -1), (0, -2), (0, -1), (1, -2), (1, -1)}, {(-4, 1), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)}, 20⟩
theorem entry_545_checked : entryAt 545 = entry_545 := by
  rw [entry_chunk_26 19 (by decide)]
  decide +kernel
theorem row_545 : rowAt 545 = data_545 := by
  rw [rowAt, dif_neg (by decide : ¬ 545 < 6), entry_545_checked]
  change forkRow [placeRow ⟨256, 0, 4, 5⟩ (rowAt 256), placeRow ⟨448, 0, 5, 4⟩ (rowAt 448), placeRow ⟨153, 0, 6, 3⟩ (rowAt 153), placeRow ⟨343, 0, 4, 5⟩ (rowAt 343)] = data_545
  rw [row_256, row_448, row_153, row_343]
  apply row_ext <;> decide +kernel
theorem entry_good_545 : EntryGood 545 := by
  unfold EntryGood
  rw [entry_545_checked]
  decide +kernel
theorem good_545 : Good (rowAt 545) := by
  rw [row_545]
  unfold Good
  decide +kernel

def data_546 : RowData := ⟨{(1, 0), (2, 0), (3, -2), (3, 0)}, {(-2, -1), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -3), (2, -2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -2), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)}, 21⟩
theorem entry_546_checked : entryAt 546 = entry_546 := by
  rw [entry_chunk_27 0 (by decide)]
  decide +kernel
theorem row_546 : rowAt 546 = data_546 := by
  rw [rowAt, dif_neg (by decide : ¬ 546 < 6), entry_546_checked]
  change forkRow [placeRow ⟨64, 0, 4, 3⟩ (rowAt 64), placeRow ⟨482, 7, 4, 3⟩ (rowAt 482), placeRow ⟨443, 0, 7, 5⟩ (rowAt 443), placeRow ⟨64, 6, 7, 5⟩ (rowAt 64)] = data_546
  rw [row_64, row_482, row_443]
  apply row_ext <;> decide +kernel
theorem entry_good_546 : EntryGood 546 := by
  unfold EntryGood
  rw [entry_546_checked]
  decide +kernel
theorem good_546 : Good (rowAt 546) := by
  rw [row_546]
  unfold Good
  decide +kernel

def data_547 : RowData := ⟨{(1, -1), (1, 0), (2, 0), (3, 0)}, {(-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)}, 21⟩
theorem entry_547_checked : entryAt 547 = entry_547 := by
  rw [entry_chunk_27 1 (by decide)]
  decide +kernel
theorem row_547 : rowAt 547 = data_547 := by
  rw [rowAt, dif_neg (by decide : ¬ 547 < 6), entry_547_checked]
  change forkRow [placeRow ⟨443, 0, 7, 5⟩ (rowAt 443), placeRow ⟨510, 4, 7, 5⟩ (rowAt 510), placeRow ⟨131, 3, 3, 4⟩ (rowAt 131)] = data_547
  rw [row_443, row_510, row_131]
  apply row_ext <;> decide +kernel
theorem entry_good_547 : EntryGood 547 := by
  unfold EntryGood
  rw [entry_547_checked]
  decide +kernel
theorem good_547 : Good (rowAt 547) := by
  rw [row_547]
  unfold Good
  decide +kernel

def data_548 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1)}, {(-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3)}, 15⟩
theorem entry_548_checked : entryAt 548 = entry_548 := by
  rw [entry_chunk_27 2 (by decide)]
  decide +kernel
theorem row_548 : rowAt 548 = data_548 := by
  rw [rowAt, dif_neg (by decide : ¬ 548 < 6), entry_548_checked]
  change forkRow [placeRow ⟨426, 0, 4, 5⟩ (rowAt 426), placeRow ⟨541, 0, 4, 5⟩ (rowAt 541), placeRow ⟨25, 0, 5, 4⟩ (rowAt 25), placeRow ⟨321, 4, 4, 2⟩ (rowAt 321)] = data_548
  rw [row_426, row_541, row_25, row_321]
  apply row_ext <;> decide +kernel
theorem entry_good_548 : EntryGood 548 := by
  unfold EntryGood
  rw [entry_548_checked]
  decide +kernel
theorem good_548 : Good (rowAt 548) := by
  rw [row_548]
  unfold Good
  decide +kernel

def data_549 : RowData := ⟨{(-2, -3), (-1, 0), (1, 0)}, {(-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4)}, 17⟩
theorem entry_549_checked : entryAt 549 = entry_549 := by
  rw [entry_chunk_27 3 (by decide)]
  decide +kernel
theorem row_549 : rowAt 549 = data_549 := by
  rw [rowAt, dif_neg (by decide : ¬ 549 < 6), entry_549_checked]
  change forkRow [placeRow ⟨385, 0, 6, 4⟩ (rowAt 385), placeRow ⟨385, 4, 2, 4⟩ (rowAt 385), placeRow ⟨330, 0, 6, 4⟩ (rowAt 330), placeRow ⟨252, 6, 2, 4⟩ (rowAt 252), placeRow ⟨326, 0, 6, 4⟩ (rowAt 326), placeRow ⟨529, 0, 2, 4⟩ (rowAt 529)] = data_549
  rw [row_385, row_330, row_252, row_326, row_529]
  apply row_ext <;> decide +kernel
theorem entry_good_549 : EntryGood 549 := by
  unfold EntryGood
  rw [entry_549_checked]
  decide +kernel
theorem good_549 : Good (rowAt 549) := by
  rw [row_549]
  unfold Good
  decide +kernel

def data_550 : RowData := ⟨{(0, -1), (0, 1), (2, 1)}, {(-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 2), (5, 3), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2), (7, 3)}, 13⟩
theorem entry_550_checked : entryAt 550 = entry_550 := by
  rw [entry_chunk_27 4 (by decide)]
  decide +kernel
theorem row_550 : rowAt 550 = data_550 := by
  rw [rowAt, dif_neg (by decide : ¬ 550 < 6), entry_550_checked]
  change forkRow [placeRow ⟨424, 0, 4, 6⟩ (rowAt 424), placeRow ⟨172, 7, 4, 2⟩ (rowAt 172), placeRow ⟨215, 1, 5, 5⟩ (rowAt 215), placeRow ⟨456, 7, 4, 2⟩ (rowAt 456)] = data_550
  rw [row_424, row_172, row_215, row_456]
  apply row_ext <;> decide +kernel
theorem entry_good_550 : EntryGood 550 := by
  unfold EntryGood
  rw [entry_550_checked]
  decide +kernel
theorem good_550 : Good (rowAt 550) := by
  rw [row_550]
  unfold Good
  decide +kernel

def data_551 : RowData := ⟨{(0, 1), (0, 2)}, {(-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 4), (6, 4)}, 14⟩
theorem entry_551_checked : entryAt 551 = entry_551 := by
  rw [entry_chunk_27 5 (by decide)]
  decide +kernel
theorem row_551 : rowAt 551 = data_551 := by
  rw [rowAt, dif_neg (by decide : ¬ 551 < 6), entry_551_checked]
  change forkRow [placeRow ⟨300, 6, 4, 3⟩ (rowAt 300), placeRow ⟨172, 7, 4, 3⟩ (rowAt 172), placeRow ⟨319, 3, 5, 7⟩ (rowAt 319), placeRow ⟨527, 4, 5, 7⟩ (rowAt 527), placeRow ⟨176, 5, 4, 3⟩ (rowAt 176)] = data_551
  rw [row_300, row_172, row_319, row_527, row_176]
  apply row_ext <;> decide +kernel
theorem entry_good_551 : EntryGood 551 := by
  unfold EntryGood
  rw [entry_551_checked]
  decide +kernel
theorem good_551 : Good (rowAt 551) := by
  rw [row_551]
  unfold Good
  decide +kernel

def data_552 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -3), (4, -2), (4, -1), (4, 1), (5, -1)}, 21⟩
theorem entry_552_checked : entryAt 552 = entry_552 := by
  rw [entry_chunk_27 6 (by decide)]
  decide +kernel
theorem row_552 : rowAt 552 = data_552 := by
  rw [rowAt, dif_neg (by decide : ¬ 552 < 6), entry_552_checked]
  change forkRow [placeRow ⟨443, 4, 1, 5⟩ (rowAt 443), placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨504, 1, 3, 3⟩ (rowAt 504), placeRow ⟨404, 5, 2, 3⟩ (rowAt 404)] = data_552
  rw [row_443, row_64, row_504, row_404]
  apply row_ext <;> decide +kernel
theorem entry_good_552 : EntryGood 552 := by
  unfold EntryGood
  rw [entry_552_checked]
  decide +kernel
theorem good_552 : Good (rowAt 552) := by
  rw [row_552]
  unfold Good
  decide +kernel

def data_553 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)}, 17⟩
theorem entry_553_checked : entryAt 553 = entry_553 := by
  rw [entry_chunk_27 7 (by decide)]
  decide +kernel
theorem row_553 : rowAt 553 = data_553 := by
  rw [rowAt, dif_neg (by decide : ¬ 553 < 6), entry_553_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨261, 4, 5, 4⟩ (rowAt 261), placeRow ⟨471, 0, 5, 1⟩ (rowAt 471), placeRow ⟨442, 0, 4, 5⟩ (rowAt 442), placeRow ⟨504, 0, 3, 3⟩ (rowAt 504), placeRow ⟨180, 0, 4, 5⟩ (rowAt 180)] = data_553
  rw [row_63, row_261, row_471, row_442, row_504, row_180]
  apply row_ext <;> decide +kernel
theorem entry_good_553 : EntryGood 553 := by
  unfold EntryGood
  rw [entry_553_checked]
  decide +kernel
theorem good_553 : Good (rowAt 553) := by
  rw [row_553]
  unfold Good
  decide +kernel

def data_554 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (1, 1), (2, 1), (3, 1)}, {(-3, 3), (-3, 5), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 0), (4, 1), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 5)}, 22⟩
theorem entry_554_checked : entryAt 554 = entry_554 := by
  rw [entry_chunk_27 8 (by decide)]
  decide +kernel
theorem row_554 : rowAt 554 = data_554 := by
  rw [rowAt, dif_neg (by decide : ¬ 554 < 6), entry_554_checked]
  change forkRow [placeRow ⟨30, 6, 5, 4⟩ (rowAt 30), placeRow ⟨96, 7, 4, 5⟩ (rowAt 96), placeRow ⟨474, 0, 4, 5⟩ (rowAt 474)] = data_554
  rw [row_30, row_96, row_474]
  apply row_ext <;> decide +kernel
theorem entry_good_554 : EntryGood 554 := by
  unfold EntryGood
  rw [entry_554_checked]
  decide +kernel
theorem good_554 : Good (rowAt 554) := by
  rw [row_554]
  unfold Good
  decide +kernel

def data_555 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (4, 3), (5, 1)}, 21⟩
theorem entry_555_checked : entryAt 555 = entry_555 := by
  rw [entry_chunk_27 9 (by decide)]
  decide +kernel
theorem row_555 : rowAt 555 = data_555 := by
  rw [rowAt, dif_neg (by decide : ¬ 555 < 6), entry_555_checked]
  change forkRow [placeRow ⟨504, 5, 3, 5⟩ (rowAt 504), placeRow ⟨513, 0, 1, 5⟩ (rowAt 513), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨443, 4, 1, 5⟩ (rowAt 443), placeRow ⟨471, 1, 1, 5⟩ (rowAt 471)] = data_555
  rw [row_504, row_513, row_55, row_443, row_471]
  apply row_ext <;> decide +kernel
theorem entry_good_555 : EntryGood 555 := by
  unfold EntryGood
  rw [entry_555_checked]
  decide +kernel
theorem good_555 : Good (rowAt 555) := by
  rw [row_555]
  unfold Good
  decide +kernel

def data_556 : RowData := ⟨{(-3, -3), (-2, -3), (-2, 0), (-1, -4), (-1, -3), (0, -3)}, {(-6, 1), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4)}, 18⟩
theorem entry_556_checked : entryAt 556 = entry_556 := by
  rw [entry_chunk_27 10 (by decide)]
  decide +kernel
theorem row_556 : rowAt 556 = data_556 := by
  rw [rowAt, dif_neg (by decide : ¬ 556 < 6), entry_556_checked]
  change forkRow [placeRow ⟨34, 1, 4, 2⟩ (rowAt 34), placeRow ⟨549, 0, 3, 4⟩ (rowAt 549)] = data_556
  rw [row_34, row_549]
  apply row_ext <;> decide +kernel
theorem entry_good_556 : EntryGood 556 := by
  unfold EntryGood
  rw [entry_556_checked]
  decide +kernel
theorem good_556 : Good (rowAt 556) := by
  rw [row_556]
  unfold Good
  decide +kernel

def data_557 : RowData := ⟨{(-1, 0)}, {(-6, -1), (-6, 0), (-6, 1), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 3), (5, 4)}, 19⟩
theorem entry_557_checked : entryAt 557 = entry_557 := by
  rw [entry_chunk_27 11 (by decide)]
  decide +kernel
theorem row_557 : rowAt 557 = data_557 := by
  rw [rowAt, dif_neg (by decide : ¬ 557 < 6), entry_557_checked]
  change forkRow [placeRow ⟨460, 0, 5, 4⟩ (rowAt 460), placeRow ⟨460, 4, 2, 4⟩ (rowAt 460), placeRow ⟨460, 2, 5, 4⟩ (rowAt 460), placeRow ⟨411, 4, 5, 4⟩ (rowAt 411), placeRow ⟨531, 0, 3, 6⟩ (rowAt 531), placeRow ⟨531, 4, 4, 6⟩ (rowAt 531), placeRow ⟨406, 5, 5, 4⟩ (rowAt 406)] = data_557
  rw [row_460, row_411, row_531, row_406]
  apply row_ext <;> decide +kernel
theorem entry_good_557 : EntryGood 557 := by
  unfold EntryGood
  rw [entry_557_checked]
  decide +kernel
theorem good_557 : Good (rowAt 557) := by
  rw [row_557]
  unfold Good
  decide +kernel

def data_558 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4)}, 21⟩
theorem entry_558_checked : entryAt 558 = entry_558 := by
  rw [entry_chunk_27 12 (by decide)]
  decide +kernel
theorem row_558 : rowAt 558 = data_558 := by
  rw [rowAt, dif_neg (by decide : ¬ 558 < 6), entry_558_checked]
  change forkRow [placeRow ⟨180, 5, 5, 4⟩ (rowAt 180), placeRow ⟨443, 4, 1, 5⟩ (rowAt 443), placeRow ⟨513, 0, 1, 5⟩ (rowAt 513), placeRow ⟨442, 1, 5, 4⟩ (rowAt 442)] = data_558
  rw [row_180, row_443, row_513, row_442]
  apply row_ext <;> decide +kernel
theorem entry_good_558 : EntryGood 558 := by
  unfold EntryGood
  rw [entry_558_checked]
  decide +kernel
theorem good_558 : Good (rowAt 558) := by
  rw [row_558]
  unfold Good
  decide +kernel

def data_559 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1)}, {(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 2), (9, -4), (9, -3), (9, -2), (9, -1), (10, -4), (10, -3), (10, -2), (10, -1)}, 23⟩
theorem entry_559_checked : entryAt 559 = entry_559 := by
  rw [entry_chunk_27 13 (by decide)]
  decide +kernel
theorem row_559 : rowAt 559 = data_559 := by
  rw [rowAt, dif_neg (by decide : ¬ 559 < 6), entry_559_checked]
  change forkRow [placeRow ⟨228, 4, 5, 2⟩ (rowAt 228), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨155, 4, 4, 5⟩ (rowAt 155), placeRow ⟨538, 5, 4, 5⟩ (rowAt 538)] = data_559
  rw [row_228, row_7, row_155, row_538]
  apply row_ext <;> decide +kernel
theorem entry_good_559 : EntryGood 559 := by
  unfold EntryGood
  rw [entry_559_checked]
  decide +kernel
theorem good_559 : Good (rowAt 559) := by
  rw [row_559]
  unfold Good
  decide +kernel

def data_560 : RowData := ⟨{(-2, -1), (-2, 0), (-2, 1), (0, 1)}, {(-7, 1), (-6, 0), (-6, 1), (-5, 0), (-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -1), (8, 0), (8, 1), (9, -1), (9, 1)}, 23⟩
theorem entry_560_checked : entryAt 560 = entry_560 := by
  rw [entry_chunk_27 14 (by decide)]
  decide +kernel
theorem row_560 : rowAt 560 = data_560 := by
  rw [rowAt, dif_neg (by decide : ¬ 560 < 6), entry_560_checked]
  change forkRow [placeRow ⟨517, 5, 5, 4⟩ (rowAt 517), placeRow ⟨416, 5, 4, 3⟩ (rowAt 416), placeRow ⟨359, 5, 3, 4⟩ (rowAt 359), placeRow ⟨356, 6, 3, 4⟩ (rowAt 356), placeRow ⟨483, 0, 4, 6⟩ (rowAt 483)] = data_560
  rw [row_517, row_416, row_359, row_356, row_483]
  apply row_ext <;> decide +kernel
theorem entry_good_560 : EntryGood 560 := by
  unfold EntryGood
  rw [entry_560_checked]
  decide +kernel
theorem good_560 : Good (rowAt 560) := by
  rw [row_560]
  unfold Good
  decide +kernel

def data_561 : RowData := ⟨{(-2, -2), (-2, 0), (-1, 0)}, {(-7, 2), (-7, 4), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 4)}, 22⟩
theorem entry_561_checked : entryAt 561 = entry_561 := by
  rw [entry_chunk_27 15 (by decide)]
  decide +kernel
theorem row_561 : rowAt 561 = data_561 := by
  rw [rowAt, dif_neg (by decide : ¬ 561 < 6), entry_561_checked]
  change forkRow [placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨173, 2, 5, 4⟩ (rowAt 173), placeRow ⟨263, 6, 1, 4⟩ (rowAt 263), placeRow ⟨236, 1, 5, 5⟩ (rowAt 236), placeRow ⟨546, 4, 5, 4⟩ (rowAt 546), placeRow ⟨176, 2, 5, 4⟩ (rowAt 176), placeRow ⟨535, 0, 4, 5⟩ (rowAt 535)] = data_561
  rw [row_295, row_173, row_263, row_236, row_546, row_176, row_535]
  apply row_ext <;> decide +kernel
theorem entry_good_561 : EntryGood 561 := by
  unfold EntryGood
  rw [entry_561_checked]
  decide +kernel
theorem good_561 : Good (rowAt 561) := by
  rw [row_561]
  unfold Good
  decide +kernel

def data_562 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (0, -1)}, {(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 3), (9, -3), (9, -2), (9, -1), (9, 0), (10, -3), (10, -2), (10, -1), (10, 0)}, 24⟩
theorem entry_562_checked : entryAt 562 = entry_562 := by
  rw [entry_chunk_27 16 (by decide)]
  decide +kernel
theorem row_562 : rowAt 562 = data_562 := by
  rw [rowAt, dif_neg (by decide : ¬ 562 < 6), entry_562_checked]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (rowAt 6), placeRow ⟨559, 0, 4, 5⟩ (rowAt 559)] = data_562
  rw [row_6, row_559]
  apply row_ext <;> decide +kernel
theorem entry_good_562 : EntryGood 562 := by
  unfold EntryGood
  rw [entry_562_checked]
  decide +kernel
theorem good_562 : Good (rowAt 562) := by
  rw [row_562]
  unfold Good
  decide +kernel

def data_563 : RowData := ⟨{(1, -1), (1, 0), (2, -1), (2, 0)}, {(-5, 2), (-5, 4), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 4)}, 23⟩
theorem entry_563_checked : entryAt 563 = entry_563 := by
  rw [entry_chunk_27 17 (by decide)]
  decide +kernel
theorem row_563 : rowAt 563 = data_563 := by
  rw [rowAt, dif_neg (by decide : ¬ 563 < 6), entry_563_checked]
  change forkRow [placeRow ⟨167, 0, 7, 4⟩ (rowAt 167), placeRow ⟨538, 0, 3, 4⟩ (rowAt 538), placeRow ⟨514, 0, 7, 4⟩ (rowAt 514), placeRow ⟨330, 4, 3, 4⟩ (rowAt 330), placeRow ⟨545, 0, 5, 5⟩ (rowAt 545)] = data_563
  rw [row_167, row_538, row_514, row_330, row_545]
  apply row_ext <;> decide +kernel
theorem entry_good_563 : EntryGood 563 := by
  unfold EntryGood
  rw [entry_563_checked]
  decide +kernel
theorem good_563 : Good (rowAt 563) := by
  rw [row_563]
  unfold Good
  decide +kernel

def data_564 : RowData := ⟨{(-2, -2), (-2, -1), (-2, 0)}, {(-7, -1), (-7, 0), (-7, 1), (-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (9, -2), (9, 0)}, 24⟩
theorem entry_564_checked : entryAt 564 = entry_564 := by
  rw [entry_chunk_27 18 (by decide)]
  decide +kernel
theorem row_564 : rowAt 564 = data_564 := by
  rw [rowAt, dif_neg (by decide : ¬ 564 < 6), entry_564_checked]
  change forkRow [placeRow ⟨560, 0, 4, 3⟩ (rowAt 560), placeRow ⟨421, 0, 3, 4⟩ (rowAt 421), placeRow ⟨401, 1, 3, 4⟩ (rowAt 401), placeRow ⟨340, 3, 3, 4⟩ (rowAt 340), placeRow ⟨509, 0, 3, 4⟩ (rowAt 509), placeRow ⟨528, 0, 4, 3⟩ (rowAt 528), placeRow ⟨423, 5, 4, 3⟩ (rowAt 423), placeRow ⟨425, 5, 4, 3⟩ (rowAt 425), placeRow ⟨336, 0, 3, 4⟩ (rowAt 336)] = data_564
  rw [row_560, row_421, row_401, row_340, row_509, row_528, row_423, row_425, row_336]
  apply row_ext <;> decide +kernel
theorem entry_good_564 : EntryGood 564 := by
  unfold EntryGood
  rw [entry_564_checked]
  decide +kernel
theorem good_564 : Good (rowAt 564) := by
  rw [row_564]
  unfold Good
  decide +kernel

def data_565 : RowData := ⟨{(1, -1), (1, 0), (2, 0), (3, 0)}, {(-5, 2), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -1), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -1), (5, 0), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 4)}, 23⟩
theorem entry_565_checked : entryAt 565 = entry_565 := by
  rw [entry_chunk_27 19 (by decide)]
  decide +kernel
theorem row_565 : rowAt 565 = data_565 := by
  rw [rowAt, dif_neg (by decide : ¬ 565 < 6), entry_565_checked]
  change forkRow [placeRow ⟨443, 4, 4, 5⟩ (rowAt 443), placeRow ⟨131, 3, 3, 4⟩ (rowAt 131), placeRow ⟨538, 0, 3, 4⟩ (rowAt 538), placeRow ⟨459, 0, 5, 5⟩ (rowAt 459), placeRow ⟨144, 4, 3, 4⟩ (rowAt 144)] = data_565
  rw [row_443, row_131, row_538, row_459, row_144]
  apply row_ext <;> decide +kernel
theorem entry_good_565 : EntryGood 565 := by
  unfold EntryGood
  rw [entry_565_checked]
  decide +kernel
theorem good_565 : Good (rowAt 565) := by
  rw [row_565]
  unfold Good
  decide +kernel

def data_566 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3)}, {(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)}, 17⟩
theorem entry_566_checked : entryAt 566 = entry_566 := by
  rw [entry_chunk_28 0 (by decide)]
  decide +kernel
theorem row_566 : rowAt 566 = data_566 := by
  rw [rowAt, dif_neg (by decide : ¬ 566 < 6), entry_566_checked]
  change forkRow [placeRow ⟨314, 0, 3, 4⟩ (rowAt 314), placeRow ⟨180, 0, 4, 5⟩ (rowAt 180), placeRow ⟨442, 0, 4, 5⟩ (rowAt 442), placeRow ⟨466, 0, 6, 3⟩ (rowAt 466), placeRow ⟨504, 0, 3, 3⟩ (rowAt 504)] = data_566
  rw [row_314, row_180, row_442, row_466, row_504]
  apply row_ext <;> decide +kernel
theorem entry_good_566 : EntryGood 566 := by
  unfold EntryGood
  rw [entry_566_checked]
  decide +kernel
theorem good_566 : Good (rowAt 566) := by
  rw [row_566]
  unfold Good
  decide +kernel

def data_567 : RowData := ⟨{(-1, -4), (0, -4), (0, -3), (0, -2), (1, 0)}, {(-5, -4), (-5, -2), (-5, 2), (-5, 4), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -1), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 4)}, 23⟩
theorem entry_567_checked : entryAt 567 = entry_567 := by
  rw [entry_chunk_28 1 (by decide)]
  decide +kernel
theorem row_567 : rowAt 567 = data_567 := by
  rw [rowAt, dif_neg (by decide : ¬ 567 < 6), entry_567_checked]
  change forkRow [placeRow ⟨21, 1, 4, 3⟩ (rowAt 21), placeRow ⟨561, 0, 6, 4⟩ (rowAt 561), placeRow ⟨500, 4, 3, 1⟩ (rowAt 500)] = data_567
  rw [row_21, row_561, row_500]
  apply row_ext <;> decide +kernel
theorem entry_good_567 : EntryGood 567 := by
  unfold EntryGood
  rw [entry_567_checked]
  decide +kernel
theorem good_567 : Good (rowAt 567) := by
  rw [row_567]
  unfold Good
  decide +kernel

def data_568 : RowData := ⟨{(-1, -1), (-1, 0), (1, 0)}, {(-7, 2), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)}, 24⟩
theorem entry_568_checked : entryAt 568 = entry_568 := by
  rw [entry_chunk_28 2 (by decide)]
  decide +kernel
theorem row_568 : rowAt 568 = data_568 := by
  rw [rowAt, dif_neg (by decide : ¬ 568 < 6), entry_568_checked]
  change forkRow [placeRow ⟨538, 4, 6, 4⟩ (rowAt 538), placeRow ⟨547, 0, 2, 4⟩ (rowAt 547), placeRow ⟨275, 0, 6, 4⟩ (rowAt 275), placeRow ⟨565, 0, 2, 4⟩ (rowAt 565), placeRow ⟨330, 0, 6, 4⟩ (rowAt 330)] = data_568
  rw [row_538, row_547, row_275, row_565, row_330]
  apply row_ext <;> decide +kernel
theorem entry_good_568 : EntryGood 568 := by
  unfold EntryGood
  rw [entry_568_checked]
  decide +kernel
theorem good_568 : Good (rowAt 568) := by
  rw [row_568]
  unfold Good
  decide +kernel

def data_569 : RowData := ⟨{(0, -3), (1, -4), (1, -3), (2, -3), (2, -1), (2, 0), (3, -3)}, {(-5, 2), (-5, 4), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -1), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)}, 25⟩
theorem entry_569_checked : entryAt 569 = entry_569 := by
  rw [entry_chunk_28 3 (by decide)]
  decide +kernel
theorem row_569 : rowAt 569 = data_569 := by
  rw [rowAt, dif_neg (by decide : ¬ 569 < 6), entry_569_checked]
  change forkRow [placeRow ⟨34, 3, 4, 2⟩ (rowAt 34), placeRow ⟨568, 4, 5, 4⟩ (rowAt 568)] = data_569
  rw [row_34, row_568]
  apply row_ext <;> decide +kernel
theorem entry_good_569 : EntryGood 569 := by
  unfold EntryGood
  rw [entry_569_checked]
  decide +kernel
theorem good_569 : Good (rowAt 569) := by
  rw [row_569]
  unfold Good
  decide +kernel

def data_570 : RowData := ⟨{(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2)}, {(-7, 3), (-7, 5), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (6, 3), (6, 5)}, 26⟩
theorem entry_570_checked : entryAt 570 = entry_570 := by
  rw [entry_chunk_28 4 (by decide)]
  decide +kernel
theorem row_570 : rowAt 570 = data_570 := by
  rw [rowAt, dif_neg (by decide : ¬ 570 < 6), entry_570_checked]
  change forkRow [placeRow ⟨569, 0, 2, 5⟩ (rowAt 569), placeRow ⟨2, 7, 4, 3⟩ (rowAt 2)] = data_570
  rw [row_569, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_570 : EntryGood 570 := by
  unfold EntryGood
  rw [entry_570_checked]
  decide +kernel
theorem good_570 : Good (rowAt 570) := by
  rw [row_570]
  unfold Good
  decide +kernel

def data_571 : RowData := ⟨{(-2, -3), (-1, -4), (-1, -3), (0, -3), (1, -3)}, {(-7, 2), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -2), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)}, 27⟩
theorem entry_571_checked : entryAt 571 = entry_571 := by
  rw [entry_chunk_28 5 (by decide)]
  decide +kernel
theorem row_571 : rowAt 571 = data_571 := by
  rw [rowAt, dif_neg (by decide : ¬ 571 < 6), entry_571_checked]
  change forkRow [placeRow ⟨293, 0, 4, 3⟩ (rowAt 293), placeRow ⟨570, 0, 4, 3⟩ (rowAt 570), placeRow ⟨382, 0, 4, 3⟩ (rowAt 382), placeRow ⟨556, 4, 2, 4⟩ (rowAt 556)] = data_571
  rw [row_293, row_570, row_382, row_556]
  apply row_ext <;> decide +kernel
theorem entry_good_571 : EntryGood 571 := by
  unfold EntryGood
  rw [entry_571_checked]
  decide +kernel
theorem good_571 : Good (rowAt 571) := by
  rw [row_571]
  unfold Good
  decide +kernel

def data_572 : RowData := ⟨{(1, 0), (2, 0)}, {(-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -1), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 1), (8, 3), (8, 4), (8, 6)}, 25⟩
theorem entry_572_checked : entryAt 572 = entry_572 := by
  rw [entry_chunk_28 6 (by decide)]
  decide +kernel
theorem row_572 : rowAt 572 = data_572 := by
  rw [rowAt, dif_neg (by decide : ¬ 572 < 6), entry_572_checked]
  change forkRow [placeRow ⟨564, 1, 6, 6⟩ (rowAt 564), placeRow ⟨465, 3, 3, 4⟩ (rowAt 465), placeRow ⟨385, 4, 3, 4⟩ (rowAt 385), placeRow ⟨364, 7, 3, 4⟩ (rowAt 364), placeRow ⟨499, 1, 6, 5⟩ (rowAt 499)] = data_572
  rw [row_564, row_465, row_385, row_364, row_499]
  apply row_ext <;> decide +kernel
theorem entry_good_572 : EntryGood 572 := by
  unfold EntryGood
  rw [entry_572_checked]
  decide +kernel
theorem good_572 : Good (rowAt 572) := by
  rw [row_572]
  unfold Good
  decide +kernel

def data_573 : RowData := ⟨{(0, -2), (0, -1)}, {(-8, -3), (-8, -1), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -4), (6, -3), (6, -1), (6, 0), (6, 1), (7, 1)}, 19⟩
theorem entry_573_checked : entryAt 573 = entry_573 := by
  rw [entry_chunk_28 7 (by decide)]
  decide +kernel
theorem row_573 : rowAt 573 = data_573 := by
  rw [rowAt, dif_neg (by decide : ¬ 573 < 6), entry_573_checked]
  change forkRow [placeRow ⟨527, 2, 3, 1⟩ (rowAt 527), placeRow ⟨499, 4, 3, 4⟩ (rowAt 499), placeRow ⟨527, 6, 5, 1⟩ (rowAt 527), placeRow ⟨499, 0, 5, 4⟩ (rowAt 499), placeRow ⟨407, 4, 4, 1⟩ (rowAt 407), placeRow ⟨531, 7, 2, 4⟩ (rowAt 531), placeRow ⟨407, 0, 4, 1⟩ (rowAt 407)] = data_573
  rw [row_527, row_499, row_407, row_531]
  apply row_ext <;> decide +kernel
theorem entry_good_573 : EntryGood 573 := by
  unfold EntryGood
  rw [entry_573_checked]
  decide +kernel
theorem good_573 : Good (rowAt 573) := by
  rw [row_573]
  unfold Good
  decide +kernel

def data_574 : RowData := ⟨{(-1, -1), (-1, 0), (0, -1)}, {(-7, 2), (-7, 3), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (8, -2), (8, 0), (8, 2)}, 24⟩
theorem entry_574_checked : entryAt 574 = entry_574 := by
  rw [entry_chunk_28 8 (by decide)]
  decide +kernel
theorem row_574 : rowAt 574 = data_574 := by
  rw [rowAt, dif_neg (by decide : ¬ 574 < 6), entry_574_checked]
  change forkRow [placeRow ⟨497, 0, 2, 4⟩ (rowAt 497), placeRow ⟨539, 4, 4, 6⟩ (rowAt 539), placeRow ⟨355, 0, 2, 4⟩ (rowAt 355), placeRow ⟨390, 3, 2, 4⟩ (rowAt 390), placeRow ⟨544, 0, 2, 4⟩ (rowAt 544), placeRow ⟨462, 1, 4, 5⟩ (rowAt 462), placeRow ⟨563, 4, 5, 4⟩ (rowAt 563), placeRow ⟨540, 4, 4, 6⟩ (rowAt 540), placeRow ⟨518, 0, 2, 4⟩ (rowAt 518), placeRow ⟨495, 4, 2, 4⟩ (rowAt 495)] = data_574
  rw [row_497, row_539, row_355, row_390, row_544, row_462, row_563, row_540, row_518, row_495]
  apply row_ext <;> decide +kernel
theorem entry_good_574 : EntryGood 574 := by
  unfold EntryGood
  rw [entry_574_checked]
  decide +kernel
theorem good_574 : Good (rowAt 574) := by
  rw [row_574]
  unfold Good
  decide +kernel

def data_575 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 3), (9, -3), (9, -2), (9, -1), (9, 0), (10, -3), (10, -2), (10, -1), (10, 0)}, 24⟩
theorem entry_575_checked : entryAt 575 = entry_575 := by
  rw [entry_chunk_28 9 (by decide)]
  decide +kernel
theorem row_575 : rowAt 575 = data_575 := by
  rw [rowAt, dif_neg (by decide : ¬ 575 < 6), entry_575_checked]
  change forkRow [placeRow ⟨314, 4, 5, 4⟩ (rowAt 314), placeRow ⟨504, 4, 5, 3⟩ (rowAt 504), placeRow ⟨180, 4, 4, 5⟩ (rowAt 180), placeRow ⟨442, 4, 4, 5⟩ (rowAt 442), placeRow ⟨559, 0, 4, 5⟩ (rowAt 559)] = data_575
  rw [row_314, row_504, row_180, row_442, row_559]
  apply row_ext <;> decide +kernel
theorem entry_good_575 : EntryGood 575 := by
  unfold EntryGood
  rw [entry_575_checked]
  decide +kernel
theorem good_575 : Good (rowAt 575) := by
  rw [row_575]
  unfold Good
  decide +kernel

#check row_575
def data_576 : RowData := ⟨{(-1, -1), (-1, 0), (0, -1)}, {(-9, -2), (-9, 0), (-9, 2), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 2), (6, 3), (6, 4)}, 24⟩
theorem entry_576_checked : entryAt 576 = entry_576 := by
  rw [entry_chunk_28 10 (by decide)]
  decide +kernel
theorem row_576 : rowAt 576 = data_576 := by
  rw [rowAt, dif_neg (by decide : ¬ 576 < 6), entry_576_checked]
  change forkRow [placeRow ⟨495, 0, 5, 4⟩ (rowAt 495), placeRow ⟨544, 4, 5, 4⟩ (rowAt 544), placeRow ⟨462, 3, 3, 5⟩ (rowAt 462), placeRow ⟨540, 0, 3, 6⟩ (rowAt 540), placeRow ⟨355, 4, 5, 4⟩ (rowAt 355), placeRow ⟨539, 0, 3, 6⟩ (rowAt 539), placeRow ⟨497, 4, 5, 4⟩ (rowAt 497), placeRow ⟨390, 1, 5, 4⟩ (rowAt 390), placeRow ⟨563, 0, 2, 4⟩ (rowAt 563), placeRow ⟨518, 4, 5, 4⟩ (rowAt 518)] = data_576
  rw [row_495, row_544, row_462, row_540, row_355, row_539, row_497, row_390, row_563, row_518]
  apply row_ext <;> decide +kernel
theorem entry_good_576 : EntryGood 576 := by
  unfold EntryGood
  rw [entry_576_checked]
  decide +kernel
theorem good_576 : Good (rowAt 576) := by
  rw [row_576]
  unfold Good
  decide +kernel

def data_577 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-9, -2), (-9, 0), (-8, -2), (-8, -1), (-8, 0), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (8, -3), (8, -2), (8, -1), (9, -3), (9, -1)}, 21⟩
theorem entry_577_checked : entryAt 577 = entry_577 := by
  rw [entry_chunk_28 11 (by decide)]
  decide +kernel
theorem row_577 : rowAt 577 = data_577 := by
  rw [rowAt, dif_neg (by decide : ¬ 577 < 6), entry_577_checked]
  change forkRow [placeRow ⟨64, 7, 5, 4⟩ (rowAt 64), placeRow ⟨64, 1, 3, 1⟩ (rowAt 64), placeRow ⟨443, 1, 5, 4⟩ (rowAt 443), placeRow ⟨443, 7, 3, 1⟩ (rowAt 443)] = data_577
  rw [row_64, row_443]
  apply row_ext <;> decide +kernel
theorem entry_good_577 : EntryGood 577 := by
  unfold EntryGood
  rw [entry_577_checked]
  decide +kernel
theorem good_577 : Good (rowAt 577) := by
  rw [row_577]
  unfold Good
  decide +kernel

def data_578 : RowData := ⟨{(0, -3), (0, -2), (1, 0), (1, 1)}, {(-8, -1), (-8, 1), (-8, 3), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 3), (7, 4), (7, 5)}, 25⟩
theorem entry_578_checked : entryAt 578 = entry_578 := by
  rw [entry_chunk_28 12 (by decide)]
  decide +kernel
theorem row_578 : rowAt 578 = data_578 := by
  rw [rowAt, dif_neg (by decide : ¬ 578 < 6), entry_578_checked]
  change forkRow [placeRow ⟨574, 4, 4, 5⟩ (rowAt 574), placeRow ⟨2, 1, 4, 3⟩ (rowAt 2)] = data_578
  rw [row_574, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_578 : EntryGood 578 := by
  unfold EntryGood
  rw [entry_578_checked]
  decide +kernel
theorem good_578 : Good (rowAt 578) := by
  rw [row_578]
  unfold Good
  decide +kernel

def data_579 : RowData := ⟨{(0, -3), (0, -2), (1, 0), (1, 1)}, {(-6, 3), (-6, 4), (-6, 5), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (9, -1), (9, 1), (9, 3)}, 25⟩
theorem entry_579_checked : entryAt 579 = entry_579 := by
  rw [entry_chunk_28 13 (by decide)]
  decide +kernel
theorem row_579 : rowAt 579 = data_579 := by
  rw [rowAt, dif_neg (by decide : ¬ 579 < 6), entry_579_checked]
  change forkRow [placeRow ⟨2, 1, 4, 3⟩ (rowAt 2), placeRow ⟨576, 4, 4, 5⟩ (rowAt 576)] = data_579
  rw [row_2, row_576]
  apply row_ext <;> decide +kernel
theorem entry_good_579 : EntryGood 579 := by
  unfold EntryGood
  rw [entry_579_checked]
  decide +kernel
theorem good_579 : Good (rowAt 579) := by
  rw [row_579]
  unfold Good
  decide +kernel

def data_580 : RowData := ⟨{(-1, -4), (-1, -3), (0, -3), (0, -1)}, {(-7, 2), (-7, 3), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (8, -2), (8, 0), (8, 2)}, 26⟩
theorem entry_580_checked : entryAt 580 = entry_580 := by
  rw [entry_chunk_28 14 (by decide)]
  decide +kernel
theorem row_580 : rowAt 580 = data_580 := by
  rw [rowAt, dif_neg (by decide : ¬ 580 < 6), entry_580_checked]
  change forkRow [placeRow ⟨2, 7, 4, 2⟩ (rowAt 2), placeRow ⟨579, 0, 3, 3⟩ (rowAt 579)] = data_580
  rw [row_2, row_579]
  apply row_ext <;> decide +kernel
theorem entry_good_580 : EntryGood 580 := by
  unfold EntryGood
  rw [entry_580_checked]
  decide +kernel
theorem good_580 : Good (rowAt 580) := by
  rw [row_580]
  unfold Good
  decide +kernel

def data_581 : RowData := ⟨{(0, -3), (0, -1), (1, -4), (1, -3)}, {(-6, 2), (-6, 3), (-6, 4), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -2), (9, 0), (9, 2)}, 26⟩
theorem entry_581_checked : entryAt 581 = entry_581 := by
  rw [entry_chunk_28 15 (by decide)]
  decide +kernel
theorem row_581 : rowAt 581 = data_581 := by
  rw [rowAt, dif_neg (by decide : ¬ 581 < 6), entry_581_checked]
  change forkRow [placeRow ⟨578, 4, 5, 3⟩ (rowAt 578), placeRow ⟨2, 5, 4, 2⟩ (rowAt 2)] = data_581
  rw [row_578, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_581 : EntryGood 581 := by
  unfold EntryGood
  rw [entry_581_checked]
  decide +kernel
theorem good_581 : Good (rowAt 581) := by
  rw [row_581]
  unfold Good
  decide +kernel

def data_582 : RowData := ⟨{(1, -4), (1, -3), (1, -2), (2, -4)}, {(-6, 1), (-6, 2), (-6, 4), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -4), (2, -3), (2, -2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 2), (6, 4), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (9, -3), (9, -2), (9, -1), (10, -3), (10, -1)}, 24⟩
theorem entry_582_checked : entryAt 582 = entry_582 := by
  rw [entry_chunk_28 16 (by decide)]
  decide +kernel
theorem row_582 : rowAt 582 = data_582 := by
  rw [rowAt, dif_neg (by decide : ¬ 582 < 6), entry_582_checked]
  change forkRow [placeRow ⟨40, 3, 4, 3⟩ (rowAt 40), placeRow ⟨446, 5, 5, 3⟩ (rowAt 446), placeRow ⟨523, 0, 7, 0⟩ (rowAt 523), placeRow ⟨480, 4, 5, 3⟩ (rowAt 480), placeRow ⟨567, 4, 5, 4⟩ (rowAt 567)] = data_582
  rw [row_40, row_446, row_523, row_480, row_567]
  apply row_ext <;> decide +kernel
theorem entry_good_582 : EntryGood 582 := by
  unfold EntryGood
  rw [entry_582_checked]
  decide +kernel
theorem good_582 : Good (rowAt 582) := by
  rw [row_582]
  unfold Good
  decide +kernel

def data_583 : RowData := ⟨{(-1, 0), (-1, 1), (-1, 2)}, {(-8, 5), (-8, 6), (-8, 8), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-6, 1), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 6), (4, 8), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1), (7, 2), (7, 3), (8, 1), (8, 3)}, 25⟩
theorem entry_583_checked : entryAt 583 = entry_583 := by
  rw [entry_chunk_28 17 (by decide)]
  decide +kernel
theorem row_583 : rowAt 583 = data_583 := by
  rw [rowAt, dif_neg (by decide : ¬ 583 < 6), entry_583_checked]
  change forkRow [placeRow ⟨25, 5, 4, 3⟩ (rowAt 25), placeRow ⟨525, 0, 5, 4⟩ (rowAt 525), placeRow ⟨582, 0, 2, 8⟩ (rowAt 582), placeRow ⟨221, 3, 3, 7⟩ (rowAt 221)] = data_583
  rw [row_25, row_525, row_582, row_221]
  apply row_ext <;> decide +kernel
theorem entry_good_583 : EntryGood 583 := by
  unfold EntryGood
  rw [entry_583_checked]
  decide +kernel
theorem good_583 : Good (rowAt 583) := by
  rw [row_583]
  unfold Good
  decide +kernel

def data_584 : RowData := ⟨{(0, -2), (0, -1)}, {(-9, -1), (-9, 1), (-8, -1), (-8, 0), (-8, 1), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 3), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (9, -2), (9, 0)}, 22⟩
theorem entry_584_checked : entryAt 584 = entry_584 := by
  rw [entry_chunk_28 18 (by decide)]
  decide +kernel
theorem row_584 : rowAt 584 = data_584 := by
  rw [rowAt, dif_neg (by decide : ¬ 584 < 6), entry_584_checked]
  change forkRow [placeRow ⟨263, 1, 4, 5⟩ (rowAt 263), placeRow ⟨236, 4, 3, 5⟩ (rowAt 236), placeRow ⟨548, 3, 3, 4⟩ (rowAt 548), placeRow ⟨295, 3, 4, 5⟩ (rowAt 295), placeRow ⟨577, 0, 4, 5⟩ (rowAt 577), placeRow ⟨173, 1, 4, 5⟩ (rowAt 173)] = data_584
  rw [row_263, row_236, row_548, row_295, row_577, row_173]
  apply row_ext <;> decide +kernel
theorem entry_good_584 : EntryGood 584 := by
  unfold EntryGood
  rw [entry_584_checked]
  decide +kernel
theorem good_584 : Good (rowAt 584) := by
  rw [row_584]
  unfold Good
  decide +kernel

def data_585 : RowData := ⟨{(0, -2), (0, -1)}, {(-9, -1), (-9, 1), (-8, -1), (-8, 0), (-8, 1), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (8, 1), (9, -2), (9, -1), (9, 0), (9, 1)}, 22⟩
theorem entry_585_checked : entryAt 585 = entry_585 := by
  rw [entry_chunk_28 19 (by decide)]
  decide +kernel
theorem row_585 : rowAt 585 = data_585 := by
  rw [rowAt, dif_neg (by decide : ¬ 585 < 6), entry_585_checked]
  change forkRow [placeRow ⟨236, 2, 5, 1⟩ (rowAt 236), placeRow ⟨300, 4, 4, 5⟩ (rowAt 300), placeRow ⟨479, 1, 4, 5⟩ (rowAt 479), placeRow ⟨577, 0, 4, 5⟩ (rowAt 577), placeRow ⟨183, 3, 4, 5⟩ (rowAt 183), placeRow ⟨527, 6, 5, 1⟩ (rowAt 527)] = data_585
  rw [row_236, row_300, row_479, row_577, row_183, row_527]
  apply row_ext <;> decide +kernel
theorem entry_good_585 : EntryGood 585 := by
  unfold EntryGood
  rw [entry_585_checked]
  decide +kernel
theorem good_585 : Good (rowAt 585) := by
  rw [row_585]
  unfold Good
  decide +kernel

def data_586 : RowData := ⟨{(0, -2), (0, -1)}, {(-7, 3), (-7, 4), (-7, 6), (-6, 1), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (10, -2), (10, -1), (10, 0), (11, -2), (11, 0)}, 26⟩
theorem entry_586_checked : entryAt 586 = entry_586 := by
  rw [entry_chunk_29 0 (by decide)]
  decide +kernel
theorem row_586 : rowAt 586 = data_586 := by
  rw [rowAt, dif_neg (by decide : ¬ 586 < 6), entry_586_checked]
  change forkRow [placeRow ⟨465, 4, 4, 5⟩ (rowAt 465), placeRow ⟨558, 1, 4, 5⟩ (rowAt 558), placeRow ⟨385, 1, 4, 5⟩ (rowAt 385), placeRow ⟨379, 4, 4, 5⟩ (rowAt 379), placeRow ⟨524, 0, 4, 5⟩ (rowAt 524), placeRow ⟨469, 2, 4, 5⟩ (rowAt 469), placeRow ⟨467, 2, 4, 5⟩ (rowAt 467), placeRow ⟨527, 4, 5, 5⟩ (rowAt 527), placeRow ⟨553, 0, 4, 5⟩ (rowAt 553), placeRow ⟨552, 1, 4, 5⟩ (rowAt 552), placeRow ⟨555, 1, 4, 5⟩ (rowAt 555), placeRow ⟨564, 0, 6, 4⟩ (rowAt 564), placeRow ⟨583, 0, 5, 2⟩ (rowAt 583)] = data_586
  rw [row_465, row_558, row_385, row_379, row_524, row_469, row_467, row_527, row_553, row_552, row_555, row_564, row_583]
  apply row_ext <;> decide +kernel
theorem entry_good_586 : EntryGood 586 := by
  unfold EntryGood
  rw [entry_586_checked]
  decide +kernel
theorem good_586 : Good (rowAt 586) := by
  rw [row_586]
  unfold Good
  decide +kernel

def data_587 : RowData := ⟨{(0, -2), (0, -1)}, {(-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (8, 1), (9, -2), (9, -1), (9, 0), (9, 1)}, 22⟩
theorem entry_587_checked : entryAt 587 = entry_587 := by
  rw [entry_chunk_29 1 (by decide)]
  decide +kernel
theorem row_587 : rowAt 587 = data_587 := by
  rw [rowAt, dif_neg (by decide : ¬ 587 < 6), entry_587_checked]
  change forkRow [placeRow ⟨300, 2, 4, 1⟩ (rowAt 300), placeRow ⟨479, 1, 4, 5⟩ (rowAt 479), placeRow ⟨319, 3, 5, 5⟩ (rowAt 319), placeRow ⟨477, 6, 4, 1⟩ (rowAt 477), placeRow ⟨252, 3, 4, 5⟩ (rowAt 252), placeRow ⟨467, 2, 4, 5⟩ (rowAt 467)] = data_587
  rw [row_300, row_479, row_319, row_477, row_252, row_467]
  apply row_ext <;> decide +kernel
theorem entry_good_587 : EntryGood 587 := by
  unfold EntryGood
  rw [entry_587_checked]
  decide +kernel
theorem good_587 : Good (rowAt 587) := by
  rw [row_587]
  unfold Good
  decide +kernel

def data_588 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (0, -1)}, {(-7, 4), (-7, 5), (-7, 7), (-6, 2), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (10, -1), (10, 0), (10, 1), (11, -1), (11, 1)}, 27⟩
theorem entry_588_checked : entryAt 588 = entry_588 := by
  rw [entry_chunk_29 2 (by decide)]
  decide +kernel
theorem row_588 : rowAt 588 = data_588 := by
  rw [rowAt, dif_neg (by decide : ¬ 588 < 6), entry_588_checked]
  change forkRow [placeRow ⟨3, 1, 3, 3⟩ (rowAt 3), placeRow ⟨586, 0, 4, 5⟩ (rowAt 586)] = data_588
  rw [row_3, row_586]
  apply row_ext <;> decide +kernel
theorem entry_good_588 : EntryGood 588 := by
  unfold EntryGood
  rw [entry_588_checked]
  decide +kernel
theorem good_588 : Good (rowAt 588) := by
  rw [row_588]
  unfold Good
  decide +kernel

def data_589 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (-1, -1)}, {(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)}, 28⟩
theorem entry_589_checked : entryAt 589 = entry_589 := by
  rw [entry_chunk_29 3 (by decide)]
  decide +kernel
theorem row_589 : rowAt 589 = data_589 := by
  rw [rowAt, dif_neg (by decide : ¬ 589 < 6), entry_589_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨588, 0, 4, 5⟩ (rowAt 588)] = data_589
  rw [row_4, row_588]
  apply row_ext <;> decide +kernel
theorem entry_good_589 : EntryGood 589 := by
  unfold EntryGood
  rw [entry_589_checked]
  decide +kernel
theorem good_589 : Good (rowAt 589) := by
  rw [row_589]
  unfold Good
  decide +kernel

def data_590 : RowData := ⟨{(0, 1), (0, 2)}, {(-9, 1), (-9, 3), (-8, 1), (-8, 2), (-8, 3), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, 0), (9, 2), (9, 3), (9, 4), (9, 5), (10, 2), (10, 3), (10, 4), (10, 5)}, 23⟩
theorem entry_590_checked : entryAt 590 = entry_590 := by
  rw [entry_chunk_29 4 (by decide)]
  decide +kernel
theorem row_590 : rowAt 590 = data_590 := by
  rw [rowAt, dif_neg (by decide : ¬ 590 < 6), entry_590_checked]
  change forkRow [placeRow ⟨295, 7, 4, 3⟩ (rowAt 295), placeRow ⟨173, 7, 4, 3⟩ (rowAt 173), placeRow ⟨577, 0, 4, 7⟩ (rowAt 577), placeRow ⟨490, 0, 4, 7⟩ (rowAt 490), placeRow ⟨217, 5, 4, 3⟩ (rowAt 217)] = data_590
  rw [row_295, row_173, row_577, row_490, row_217]
  apply row_ext <;> decide +kernel
theorem entry_good_590 : EntryGood 590 := by
  unfold EntryGood
  rw [entry_590_checked]
  decide +kernel
theorem good_590 : Good (rowAt 590) := by
  rw [row_590]
  unfold Good
  decide +kernel

def data_591 : RowData := ⟨{(0, -2), (0, -1)}, {(-10, -1), (-10, 0), (-10, 1), (-10, 2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-8, -4), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -4), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -1), (9, 0), (9, 1), (9, 2), (10, -1), (10, 0), (10, 1), (10, 2)}, 23⟩
theorem entry_591_checked : entryAt 591 = entry_591 := by
  rw [entry_chunk_29 5 (by decide)]
  decide +kernel
theorem row_591 : rowAt 591 = data_591 := by
  rw [rowAt, dif_neg (by decide : ¬ 591 < 6), entry_591_checked]
  change forkRow [placeRow ⟨524, 0, 4, 5⟩ (rowAt 524), placeRow ⟨529, 1, 4, 1⟩ (rowAt 529), placeRow ⟨529, 3, 4, 1⟩ (rowAt 529), placeRow ⟨538, 1, 4, 1⟩ (rowAt 538), placeRow ⟨538, 3, 4, 1⟩ (rowAt 538), placeRow ⟨197, 5, 4, 1⟩ (rowAt 197)] = data_591
  rw [row_524, row_529, row_538, row_197]
  apply row_ext <;> decide +kernel
theorem entry_good_591 : EntryGood 591 := by
  unfold EntryGood
  rw [entry_591_checked]
  decide +kernel
theorem good_591 : Good (rowAt 591) := by
  rw [row_591]
  unfold Good
  decide +kernel

def data_592 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1)}, {(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, -6), (-2, -5), (-2, -4), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -6), (0, -5), (0, -4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)}, 28⟩
theorem entry_592_checked : entryAt 592 = entry_592 := by
  rw [entry_chunk_29 6 (by decide)]
  decide +kernel
theorem row_592 : rowAt 592 = data_592 := by
  rw [rowAt, dif_neg (by decide : ¬ 592 < 6), entry_592_checked]
  change forkRow [placeRow ⟨588, 0, 4, 5⟩ (rowAt 588), placeRow ⟨108, 7, 3, 0⟩ (rowAt 108)] = data_592
  rw [row_588, row_108]
  apply row_ext <;> decide +kernel
theorem entry_good_592 : EntryGood 592 := by
  unfold EntryGood
  rw [entry_592_checked]
  decide +kernel
theorem good_592 : Good (rowAt 592) := by
  rw [row_592]
  unfold Good
  decide +kernel

def data_593 : RowData := ⟨{(-1, -4), (-1, -3), (0, -3), (0, -1)}, {(-7, 4), (-7, 5), (-7, 7), (-6, 2), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (10, -1), (10, 0), (10, 1), (11, -1), (11, 1)}, 27⟩
theorem entry_593_checked : entryAt 593 = entry_593 := by
  rw [entry_chunk_29 7 (by decide)]
  decide +kernel
theorem row_593 : rowAt 593 = data_593 := by
  rw [rowAt, dif_neg (by decide : ¬ 593 < 6), entry_593_checked]
  change forkRow [placeRow ⟨2, 7, 4, 2⟩ (rowAt 2), placeRow ⟨586, 0, 4, 5⟩ (rowAt 586)] = data_593
  rw [row_2, row_586]
  apply row_ext <;> decide +kernel
theorem entry_good_593 : EntryGood 593 := by
  unfold EntryGood
  rw [entry_593_checked]
  decide +kernel
theorem good_593 : Good (rowAt 593) := by
  rw [row_593]
  unfold Good
  decide +kernel

def data_594 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1)}, {(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, -3), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)}, 28⟩
theorem entry_594_checked : entryAt 594 = entry_594 := by
  rw [entry_chunk_29 8 (by decide)]
  decide +kernel
theorem row_594 : rowAt 594 = data_594 := by
  rw [rowAt, dif_neg (by decide : ¬ 594 < 6), entry_594_checked]
  change forkRow [placeRow ⟨30, 1, 4, 3⟩ (rowAt 30), placeRow ⟨476, 1, 4, 3⟩ (rowAt 476), placeRow ⟨588, 0, 4, 5⟩ (rowAt 588)] = data_594
  rw [row_30, row_476, row_588]
  apply row_ext <;> decide +kernel
theorem entry_good_594 : EntryGood 594 := by
  unfold EntryGood
  rw [entry_594_checked]
  decide +kernel
theorem good_594 : Good (rowAt 594) := by
  rw [row_594]
  unfold Good
  decide +kernel

def data_595 : RowData := ⟨{(-1, 0)}, {(-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (10, -5), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (11, -3), (11, -2), (11, -1), (12, -3), (12, -1)}, 27⟩
theorem entry_595_checked : entryAt 595 = entry_595 := by
  rw [entry_chunk_29 9 (by decide)]
  decide +kernel
theorem row_595 : rowAt 595 = data_595 := by
  rw [rowAt, dif_neg (by decide : ¬ 595 < 6), entry_595_checked]
  change forkRow [placeRow ⟨460, 4, 2, 4⟩ (rowAt 460), placeRow ⟨460, 2, 5, 4⟩ (rowAt 460), placeRow ⟨586, 1, 5, 4⟩ (rowAt 586), placeRow ⟨411, 4, 5, 4⟩ (rowAt 411), placeRow ⟨551, 1, 2, 4⟩ (rowAt 551), placeRow ⟨406, 5, 5, 4⟩ (rowAt 406), placeRow ⟨572, 0, 2, 4⟩ (rowAt 572)] = data_595
  rw [row_460, row_586, row_411, row_551, row_406, row_572]
  apply row_ext <;> decide +kernel
theorem entry_good_595 : EntryGood 595 := by
  unfold EntryGood
  rw [entry_595_checked]
  decide +kernel
theorem good_595 : Good (rowAt 595) := by
  rw [row_595]
  unfold Good
  decide +kernel

def data_596 : RowData := ⟨{(0, -1), (0, 1)}, {(-6, 7), (-6, 8), (-6, 10), (-5, 5), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 2), (11, 3), (11, 4), (12, 2), (12, 4)}, 29⟩
theorem entry_596_checked : entryAt 596 = entry_596 := by
  rw [entry_chunk_29 10 (by decide)]
  decide +kernel
theorem row_596 : rowAt 596 = data_596 := by
  rw [rowAt, dif_neg (by decide : ¬ 596 < 6), entry_596_checked]
  change forkRow [placeRow ⟨385, 5, 4, 2⟩ (rowAt 385), placeRow ⟨592, 0, 5, 6⟩ (rowAt 592), placeRow ⟨330, 1, 4, 6⟩ (rowAt 330), placeRow ⟨529, 5, 4, 6⟩ (rowAt 529), placeRow ⟨385, 1, 4, 6⟩ (rowAt 385), placeRow ⟨330, 5, 4, 2⟩ (rowAt 330)] = data_596
  rw [row_385, row_592, row_330, row_529]
  apply row_ext <;> decide +kernel
theorem entry_good_596 : EntryGood 596 := by
  unfold EntryGood
  rw [entry_596_checked]
  decide +kernel
theorem good_596 : Good (rowAt 596) := by
  rw [row_596]
  unfold Good
  decide +kernel

def data_597 : RowData := ⟨{(-1, -1), (-1, 0), (1, 0)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -4), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -2), (14, -1), (14, 0), (15, -2), (15, 0)}, 29⟩
theorem entry_597_checked : entryAt 597 = entry_597 := by
  rw [entry_chunk_29 11 (by decide)]
  decide +kernel
theorem row_597 : rowAt 597 = data_597 := by
  rw [rowAt, dif_neg (by decide : ¬ 597 < 6), entry_597_checked]
  change forkRow [placeRow ⟨24, 6, 2, 3⟩ (rowAt 24), placeRow ⟨221, 0, 6, 4⟩ (rowAt 221), placeRow ⟨199, 3, 2, 4⟩ (rowAt 199), placeRow ⟨594, 1, 6, 5⟩ (rowAt 594)] = data_597
  rw [row_24, row_221, row_199, row_594]
  apply row_ext <;> decide +kernel
theorem entry_good_597 : EntryGood 597 := by
  unfold EntryGood
  rw [entry_597_checked]
  decide +kernel
theorem good_597 : Good (rowAt 597) := by
  rw [row_597]
  unfold Good
  decide +kernel

def data_598 : RowData := ⟨{(-3, -2), (-2, -2), (-2, -1), (0, -1), (0, 1)}, {(-6, 7), (-6, 8), (-6, 10), (-5, 5), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-3, -2), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, -2), (-2, -1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, -1), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 2), (11, 3), (11, 4), (12, 2), (12, 4)}, 29⟩
theorem entry_598_checked : entryAt 598 = entry_598 := by
  rw [entry_chunk_29 12 (by decide)]
  decide +kernel
theorem row_598 : rowAt 598 = data_598 := by
  rw [rowAt, dif_neg (by decide : ¬ 598 < 6), entry_598_checked]
  change forkRow [placeRow ⟨594, 0, 5, 6⟩ (rowAt 594), placeRow ⟨456, 5, 4, 2⟩ (rowAt 456), placeRow ⟨254, 1, 3, 2⟩ (rowAt 254), placeRow ⟨554, 1, 3, 2⟩ (rowAt 554), placeRow ⟨465, 0, 4, 6⟩ (rowAt 465)] = data_598
  rw [row_594, row_456, row_254, row_554, row_465]
  apply row_ext <;> decide +kernel
theorem entry_good_598 : EntryGood 598 := by
  unfold EntryGood
  rw [entry_598_checked]
  decide +kernel
theorem good_598 : Good (rowAt 598) := by
  rw [row_598]
  unfold Good
  decide +kernel

def data_599 : RowData := ⟨{(0, -3), (0, -1), (1, -4), (1, -3)}, {(-11, -1), (-11, 1), (-10, -1), (-10, 0), (-10, 1), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 7), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -2), (9, 0), (9, 2)}, 27⟩
theorem entry_599_checked : entryAt 599 = entry_599 := by
  rw [entry_chunk_29 13 (by decide)]
  decide +kernel
theorem row_599 : rowAt 599 = data_599 := by
  rw [rowAt, dif_neg (by decide : ¬ 599 < 6), entry_599_checked]
  change forkRow [placeRow ⟨578, 4, 5, 3⟩ (rowAt 578), placeRow ⟨492, 0, 3, 1⟩ (rowAt 492), placeRow ⟨512, 4, 3, 1⟩ (rowAt 512), placeRow ⟨586, 4, 4, 5⟩ (rowAt 586), placeRow ⟨485, 0, 5, 3⟩ (rowAt 485), placeRow ⟨579, 4, 5, 3⟩ (rowAt 579)] = data_599
  rw [row_578, row_492, row_512, row_586, row_485, row_579]
  apply row_ext <;> decide +kernel
theorem entry_good_599 : EntryGood 599 := by
  unfold EntryGood
  rw [entry_599_checked]
  decide +kernel
theorem good_599 : Good (rowAt 599) := by
  rw [row_599]
  unfold Good
  decide +kernel

def data_600 : RowData := ⟨{(-2, 0), (-1, 0), (-1, 1)}, {(-5, -1), (-5, 1), (-5, 2), (-5, 4), (-4, -5), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -11), (2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -10), (6, -9), (6, -8), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 4), (13, 0), (13, 1), (13, 2), (14, 0), (14, 2)}, 29⟩
theorem entry_600_checked : entryAt 600 = entry_600 := by
  rw [entry_chunk_29 14 (by decide)]
  decide +kernel
theorem row_600 : rowAt 600 = data_600 := by
  rw [rowAt, dif_neg (by decide : ¬ 600 < 6), entry_600_checked]
  change forkRow [placeRow ⟨448, 0, 4, 5⟩ (rowAt 448), placeRow ⟨278, 2, 1, 4⟩ (rowAt 278), placeRow ⟨592, 5, 5, 3⟩ (rowAt 592), placeRow ⟨403, 5, 5, 4⟩ (rowAt 403), placeRow ⟨146, 5, 4, 3⟩ (rowAt 146)] = data_600
  rw [row_448, row_278, row_592, row_403, row_146]
  apply row_ext <;> decide +kernel
theorem entry_good_600 : EntryGood 600 := by
  unfold EntryGood
  rw [entry_600_checked]
  decide +kernel
theorem good_600 : Good (rowAt 600) := by
  rw [row_600]
  unfold Good
  decide +kernel

def data_601 : RowData := ⟨{(0, -2), (0, -1)}, {(-9, -3), (-9, -1), (-8, -3), (-8, -2), (-8, -1), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 6), (-6, 7), (-6, 9), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, 1), (11, 2), (11, 3), (12, 1), (12, 3)}, 29⟩
theorem entry_601_checked : entryAt 601 = entry_601 := by
  rw [entry_chunk_29 15 (by decide)]
  decide +kernel
theorem row_601 : rowAt 601 = data_601 := by
  rw [rowAt, dif_neg (by decide : ¬ 601 < 6), entry_601_checked]
  change forkRow [placeRow ⟨437, 6, 4, 1⟩ (rowAt 437), placeRow ⟨553, 0, 4, 5⟩ (rowAt 553), placeRow ⟨592, 0, 5, 5⟩ (rowAt 592), placeRow ⟨236, 4, 3, 5⟩ (rowAt 236), placeRow ⟨469, 4, 4, 1⟩ (rowAt 469)] = data_601
  rw [row_437, row_553, row_592, row_236, row_469]
  apply row_ext <;> decide +kernel
theorem entry_good_601 : EntryGood 601 := by
  unfold EntryGood
  rw [entry_601_checked]
  decide +kernel
theorem good_601 : Good (rowAt 601) := by
  rw [row_601]
  unfold Good
  decide +kernel

def data_602 : RowData := ⟨{(0, 1), (0, 2)}, {(-9, -1), (-9, 1), (-8, -1), (-8, 0), (-8, 1), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 8), (-6, 9), (-6, 11), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, 3), (11, 4), (11, 5), (12, 3), (12, 5)}, 29⟩
theorem entry_602_checked : entryAt 602 = entry_602 := by
  rw [entry_chunk_29 16 (by decide)]
  decide +kernel
theorem row_602 : rowAt 602 = data_602 := by
  rw [rowAt, dif_neg (by decide : ¬ 602 < 6), entry_602_checked]
  change forkRow [placeRow ⟨553, 0, 4, 7⟩ (rowAt 553), placeRow ⟨467, 4, 4, 3⟩ (rowAt 467), placeRow ⟨592, 0, 5, 7⟩ (rowAt 592), placeRow ⟨437, 6, 4, 3⟩ (rowAt 437), placeRow ⟨236, 4, 3, 7⟩ (rowAt 236)] = data_602
  rw [row_553, row_467, row_592, row_437, row_236]
  apply row_ext <;> decide +kernel
theorem entry_good_602 : EntryGood 602 := by
  unfold EntryGood
  rw [entry_602_checked]
  decide +kernel
theorem good_602 : Good (rowAt 602) := by
  rw [row_602]
  unfold Good
  decide +kernel

def data_603 : RowData := ⟨{(-1, 0)}, {(-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (10, -5), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 5), (11, -3), (11, -2), (11, -1), (11, 1), (11, 2), (11, 3), (12, -3), (12, -1), (12, 1), (12, 3)}, 27⟩
theorem entry_603_checked : entryAt 603 = entry_603 := by
  rw [entry_chunk_29 17 (by decide)]
  decide +kernel
theorem row_603 : rowAt 603 = data_603 := by
  rw [rowAt, dif_neg (by decide : ¬ 603 < 6), entry_603_checked]
  change forkRow [placeRow ⟨505, 1, 5, 4⟩ (rowAt 505), placeRow ⟨505, 5, 5, 4⟩ (rowAt 505), placeRow ⟨586, 5, 5, 4⟩ (rowAt 586), placeRow ⟨551, 7, 5, 4⟩ (rowAt 551), placeRow ⟨531, 6, 4, 2⟩ (rowAt 531), placeRow ⟨586, 1, 5, 4⟩ (rowAt 586), placeRow ⟨585, 1, 5, 4⟩ (rowAt 585), placeRow ⟨585, 5, 5, 4⟩ (rowAt 585), placeRow ⟨551, 3, 5, 4⟩ (rowAt 551), placeRow ⟨573, 1, 5, 4⟩ (rowAt 573), placeRow ⟨533, 5, 5, 4⟩ (rowAt 533), placeRow ⟨533, 1, 5, 4⟩ (rowAt 533)] = data_603
  rw [row_505, row_586, row_551, row_531, row_585, row_573, row_533]
  apply row_ext <;> decide +kernel
theorem entry_good_603 : EntryGood 603 := by
  unfold EntryGood
  rw [entry_603_checked]
  decide +kernel
theorem good_603 : Good (rowAt 603) := by
  rw [row_603]
  unfold Good
  decide +kernel

def data_604 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -2), (0, -2)}, {(-7, -1), (-6, -1), (-6, 0), (-6, 1), (-6, 6), (-6, 7), (-6, 9), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)}, 30⟩
theorem entry_604_checked : entryAt 604 = entry_604 := by
  rw [entry_chunk_29 18 (by decide)]
  decide +kernel
theorem row_604 : rowAt 604 = data_604 := by
  rw [rowAt, dif_neg (by decide : ¬ 604 < 6), entry_604_checked]
  change forkRow [placeRow ⟨597, 0, 3, 4⟩ (rowAt 597), placeRow ⟨375, 2, 4, 3⟩ (rowAt 375), placeRow ⟨597, 1, 4, 3⟩ (rowAt 597), placeRow ⟨375, 3, 3, 4⟩ (rowAt 375), placeRow ⟨350, 3, 4, 3⟩ (rowAt 350), placeRow ⟨350, 2, 3, 4⟩ (rowAt 350)] = data_604
  rw [row_597, row_375, row_350]
  apply row_ext <;> decide +kernel
theorem entry_good_604 : EntryGood 604 := by
  unfold EntryGood
  rw [entry_604_checked]
  decide +kernel
theorem good_604 : Good (rowAt 604) := by
  rw [row_604]
  unfold Good
  decide +kernel

def data_605 : RowData := ⟨{(-3, -3), (-2, -3), (-2, -2), (-2, 0), (0, -2)}, {(-7, -1), (-7, 0), (-7, 1), (-7, 2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 6), (-6, 7), (-6, 9), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -3), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)}, 30⟩
theorem entry_605_checked : entryAt 605 = entry_605 := by
  rw [entry_chunk_29 19 (by decide)]
  decide +kernel
theorem row_605 : rowAt 605 = data_605 := by
  rw [rowAt, dif_neg (by decide : ¬ 605 < 6), entry_605_checked]
  change forkRow [placeRow ⟨400, 5, 4, 3⟩ (rowAt 400), placeRow ⟨383, 6, 3, 4⟩ (rowAt 383), placeRow ⟨530, 4, 4, 3⟩ (rowAt 530), placeRow ⟨596, 1, 3, 4⟩ (rowAt 596), placeRow ⟨522, 2, 4, 3⟩ (rowAt 522), placeRow ⟨598, 0, 4, 3⟩ (rowAt 598), placeRow ⟨537, 3, 3, 4⟩ (rowAt 537), placeRow ⟨520, 1, 4, 3⟩ (rowAt 520), placeRow ⟨550, 4, 4, 3⟩ (rowAt 550)] = data_605
  rw [row_400, row_383, row_530, row_596, row_522, row_598, row_537, row_520, row_550]
  apply row_ext <;> decide +kernel
theorem entry_good_605 : EntryGood 605 := by
  unfold EntryGood
  rw [entry_605_checked]
  decide +kernel
theorem good_605 : Good (rowAt 605) := by
  rw [row_605]
  unfold Good
  decide +kernel

def data_606 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (2, -2)}, {(-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 6), (-4, 7), (-4, 9), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -4), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (15, -2), (15, -1), (15, 0), (16, -2), (16, 0)}, 31⟩
theorem entry_606_checked : entryAt 606 = entry_606 := by
  rw [entry_chunk_30 0 (by decide)]
  decide +kernel
theorem row_606 : rowAt 606 = data_606 := by
  rw [rowAt, dif_neg (by decide : ¬ 606 < 6), entry_606_checked]
  change forkRow [placeRow ⟨123, 1, 4, 3⟩ (rowAt 123), placeRow ⟨274, 0, 4, 3⟩ (rowAt 274), placeRow ⟨605, 0, 6, 4⟩ (rowAt 605), placeRow ⟨119, 1, 4, 3⟩ (rowAt 119)] = data_606
  rw [row_123, row_274, row_605, row_119]
  apply row_ext <;> decide +kernel
theorem entry_good_606 : EntryGood 606 := by
  unfold EntryGood
  rw [entry_606_checked]
  decide +kernel
theorem good_606 : Good (rowAt 606) := by
  rw [row_606]
  unfold Good
  decide +kernel

def data_607 : RowData := ⟨{(-1, -2), (0, -3), (0, -2), (0, -1)}, {(-7, -1), (-7, 0), (-7, 1), (-7, 2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 6), (-6, 7), (-6, 9), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 3), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1)}, 29⟩
theorem entry_607_checked : entryAt 607 = entry_607 := by
  rw [entry_chunk_30 1 (by decide)]
  decide +kernel
theorem row_607 : rowAt 607 = data_607 := by
  rw [rowAt, dif_neg (by decide : ¬ 607 < 6), entry_607_checked]
  change forkRow [placeRow ⟨420, 3, 1, 2⟩ (rowAt 420), placeRow ⟨419, 3, 1, 4⟩ (rowAt 419), placeRow ⟨589, 0, 5, 5⟩ (rowAt 589), placeRow ⟨314, 0, 3, 4⟩ (rowAt 314), placeRow ⟨571, 1, 7, 3⟩ (rowAt 571)] = data_607
  rw [row_420, row_419, row_589, row_314, row_571]
  apply row_ext <;> decide +kernel
theorem entry_good_607 : EntryGood 607 := by
  unfold EntryGood
  rw [entry_607_checked]
  decide +kernel
theorem good_607 : Good (rowAt 607) := by
  rw [row_607]
  unfold Good
  decide +kernel

#check row_607
def data_608 : RowData := ⟨{(-1, -3), (-1, -2), (0, -2)}, {(-9, -1), (-9, 1), (-9, 3), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 8), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -4), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (15, -2), (15, -1), (15, 0), (16, -2), (16, 0)}, 32⟩
theorem entry_608_checked : entryAt 608 = entry_608 := by
  rw [entry_chunk_30 2 (by decide)]
  decide +kernel
theorem row_608 : rowAt 608 = data_608 := by
  rw [rowAt, dif_neg (by decide : ¬ 608 < 6), entry_608_checked]
  change forkRow [placeRow ⟨486, 4, 4, 5⟩ (rowAt 486), placeRow ⟨515, 1, 4, 5⟩ (rowAt 515), placeRow ⟨580, 0, 4, 5⟩ (rowAt 580), placeRow ⟨521, 0, 4, 5⟩ (rowAt 521), placeRow ⟨581, 4, 4, 5⟩ (rowAt 581), placeRow ⟨593, 0, 4, 5⟩ (rowAt 593), placeRow ⟨599, 4, 4, 5⟩ (rowAt 599), placeRow ⟨606, 1, 6, 2⟩ (rowAt 606)] = data_608
  rw [row_486, row_515, row_580, row_521, row_581, row_593, row_599, row_606]
  apply row_ext <;> decide +kernel
theorem entry_good_608 : EntryGood 608 := by
  unfold EntryGood
  rw [entry_608_checked]
  decide +kernel
theorem good_608 : Good (rowAt 608) := by
  rw [row_608]
  unfold Good
  decide +kernel

def data_609 : RowData := ⟨{(0, -2), (0, -1), (1, -2), (2, -2)}, {(-10, -2), (-10, -1), (-10, 0), (-10, 1), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 4), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 6), (-4, 7), (-4, 9), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -6), (3, -5), (3, -4), (3, -3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -4), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (15, -2), (15, -1), (15, 0), (16, -2), (16, 0)}, 31⟩
theorem entry_609_checked : entryAt 609 = entry_609 := by
  rw [entry_chunk_30 3 (by decide)]
  decide +kernel
theorem row_609 : rowAt 609 = data_609 := by
  rw [rowAt, dif_neg (by decide : ¬ 609 < 6), entry_609_checked]
  change forkRow [placeRow ⟨286, 4, 4, 5⟩ (rowAt 286), placeRow ⟨107, 3, 4, 5⟩ (rowAt 107), placeRow ⟨532, 4, 4, 5⟩ (rowAt 532), placeRow ⟨542, 0, 4, 5⟩ (rowAt 542), placeRow ⟨221, 3, 4, 5⟩ (rowAt 221), placeRow ⟨562, 4, 4, 5⟩ (rowAt 562), placeRow ⟨575, 4, 4, 5⟩ (rowAt 575), placeRow ⟨604, 1, 6, 4⟩ (rowAt 604)] = data_609
  rw [row_286, row_107, row_532, row_542, row_221, row_562, row_575, row_604]
  apply row_ext <;> decide +kernel
theorem entry_good_609 : EntryGood 609 := by
  unfold EntryGood
  rw [entry_609_checked]
  decide +kernel
theorem good_609 : Good (rowAt 609) := by
  rw [row_609]
  unfold Good
  decide +kernel

def data_610 : RowData := ⟨{(-2, 0), (-2, 1), (-1, 0)}, {(-12, 0), (-12, 1), (-12, 2), (-12, 3), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 6), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 8), (-6, 9), (-6, 11), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (12, -2), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (13, 0), (13, 1), (13, 2), (14, 0), (14, 2)}, 32⟩
theorem entry_610_checked : entryAt 610 = entry_610 := by
  rw [entry_chunk_30 4 (by decide)]
  decide +kernel
theorem row_610 : rowAt 610 = data_610 := by
  rw [rowAt, dif_neg (by decide : ¬ 610 < 6), entry_610_checked]
  change forkRow [placeRow ⟨221, 2, 5, 4⟩ (rowAt 221), placeRow ⟨286, 5, 5, 4⟩ (rowAt 286), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107), placeRow ⟨472, 1, 5, 4⟩ (rowAt 472), placeRow ⟨566, 1, 5, 4⟩ (rowAt 566), placeRow ⟨532, 5, 5, 4⟩ (rowAt 532), placeRow ⟨542, 1, 5, 4⟩ (rowAt 542), placeRow ⟨609, 0, 2, 6⟩ (rowAt 609)] = data_610
  rw [row_221, row_286, row_107, row_472, row_566, row_532, row_542, row_609]
  apply row_ext <;> decide +kernel
theorem entry_good_610 : EntryGood 610 := by
  unfold EntryGood
  rw [entry_610_checked]
  decide +kernel
theorem good_610 : Good (rowAt 610) := by
  rw [row_610]
  unfold Good
  decide +kernel

def data_611 : RowData := ⟨{(-2, 0), (-1, 0)}, {(-16, 0), (-16, 2), (-15, 0), (-15, 1), (-15, 2), (-14, -4), (-14, -3), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2), (-14, 4), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-11, -7), (-11, -6), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-11, 6), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-9, -10), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, -12), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)}, 29⟩
theorem entry_611_checked : entryAt 611 = entry_611 := by
  rw [entry_chunk_30 5 (by decide)]
  decide +kernel
theorem row_611 : rowAt 611 = data_611 := by
  rw [rowAt, dif_neg (by decide : ¬ 611 < 6), entry_611_checked]
  change forkRow [placeRow ⟨456, 2, 5, 4⟩ (rowAt 456), placeRow ⟨456, 4, 1, 4⟩ (rowAt 456), placeRow ⟨594, 7, 1, 3⟩ (rowAt 594), placeRow ⟨594, 1, 5, 5⟩ (rowAt 594)] = data_611
  rw [row_456, row_594]
  apply row_ext <;> decide +kernel
theorem entry_good_611 : EntryGood 611 := by
  unfold EntryGood
  rw [entry_611_checked]
  decide +kernel
theorem good_611 : Good (rowAt 611) := by
  rw [row_611]
  unfold Good
  decide +kernel

def data_612 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-17, 0), (-17, 2), (-16, 0), (-16, 1), (-16, 2), (-15, -4), (-15, -3), (-15, -2), (-15, -1), (-15, 0), (-15, 1), (-15, 2), (-15, 4), (-14, -4), (-14, -3), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2), (-14, 3), (-14, 4), (-13, -5), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -7), (-12, -6), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-12, 5), (-12, 6), (-11, -8), (-11, -7), (-11, -6), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-10, -10), (-10, -9), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6), (-9, -10), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-6, -12), (-6, -11), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 3), (-4, 5), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -5), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)}, 29⟩
theorem entry_612_checked : entryAt 612 = entry_612 := by
  rw [entry_chunk_30 6 (by decide)]
  decide +kernel
theorem row_612 : rowAt 612 = data_612 := by
  rw [rowAt, dif_neg (by decide : ¬ 612 < 6), entry_612_checked]
  change forkRow [placeRow ⟨589, 1, 5, 5⟩ (rowAt 589), placeRow ⟨589, 7, 0, 3⟩ (rowAt 589)] = data_612
  rw [row_589]
  apply row_ext <;> decide +kernel
theorem entry_good_612 : EntryGood 612 := by
  unfold EntryGood
  rw [entry_612_checked]
  decide +kernel
theorem good_612 : Good (rowAt 612) := by
  rw [row_612]
  unfold Good
  decide +kernel

def data_613 : RowData := ⟨{(-2, 0), (-1, 0), (-1, 1)}, {(-17, -2), (-17, 0), (-17, 2), (-16, -2), (-16, -1), (-16, 0), (-16, 1), (-16, 2), (-15, -4), (-15, -3), (-15, -2), (-15, -1), (-15, 0), (-15, 1), (-15, 2), (-15, 3), (-15, 4), (-14, -4), (-14, -3), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2), (-14, 3), (-14, 4), (-13, -5), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-13, 5), (-12, -7), (-12, -6), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-12, 5), (-12, 6), (-12, 7), (-11, -8), (-11, -7), (-11, -6), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-11, 6), (-11, 7), (-11, 8), (-10, -10), (-10, -9), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6), (-10, 7), (-10, 8), (-10, 9), (-10, 10), (-9, -10), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7), (-9, 8), (-9, 9), (-9, 10), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-8, 7), (-8, 8), (-8, 9), (-8, 10), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-7, 9), (-7, 10), (-6, -12), (-6, -11), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-6, 12), (-5, -12), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -13), (-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -13), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -13), (-2, -12), (-2, -11), (-2, -10), (-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -13), (-1, -12), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -13), (0, -12), (0, -11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -13), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -13), (2, -12), (2, -11), (2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -12), (4, -11), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -10), (6, -9), (6, -8), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -10), (8, -9), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -8), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, -7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (15, -2), (15, 0), (15, 2)}, 30⟩
theorem entry_613_checked : entryAt 613 = entry_613 := by
  rw [entry_chunk_30 7 (by decide)]
  decide +kernel
theorem row_613 : rowAt 613 = data_613 := by
  rw [rowAt, dif_neg (by decide : ¬ 613 < 6), entry_613_checked]
  change forkRow [placeRow ⟨607, 5, 5, 4⟩ (rowAt 607), placeRow ⟨503, 3, 1, 4⟩ (rowAt 503), placeRow ⟨592, 7, 1, 3⟩ (rowAt 592), placeRow ⟨592, 5, 5, 3⟩ (rowAt 592), placeRow ⟨607, 7, 1, 4⟩ (rowAt 607), placeRow ⟨612, 4, 1, 4⟩ (rowAt 612), placeRow ⟨612, 0, 5, 4⟩ (rowAt 612)] = data_613
  rw [row_607, row_503, row_592, row_612]
  apply row_ext <;> decide +kernel
theorem entry_good_613 : EntryGood 613 := by
  unfold EntryGood
  rw [entry_613_checked]
  decide +kernel
theorem good_613 : Good (rowAt 613) := by
  rw [row_613]
  unfold Good
  decide +kernel

def data_614 : RowData := ⟨{(1, 0), (1, 1)}, {(-15, -2), (-15, 0), (-15, 2), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-13, 5), (-13, 6), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-12, 5), (-12, 6), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-11, 6), (-11, 7), (-11, 8), (-11, 9), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6), (-10, 7), (-10, 8), (-10, 9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7), (-9, 8), (-9, 9), (-9, 10), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-8, 7), (-8, 8), (-8, 9), (-8, 10), (-8, 11), (-8, 12), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-7, 9), (-7, 10), (-7, 11), (-7, 12), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-6, 12), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-5, 12), (-5, 13), (-5, 14), (-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-3, 14), (-2, -13), (-2, -12), (-2, -11), (-2, -10), (-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -13), (-1, -12), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (-1, 16), (0, -13), (0, -12), (0, -11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (1, -13), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (1, 17), (2, -13), (2, -12), (2, -11), (2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (2, 16), (3, -13), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (3, 17), (4, -13), (4, -12), (4, -11), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (5, -12), (5, -11), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (6, -12), (6, -11), (6, -10), (6, -9), (6, -8), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 15), (8, -10), (8, -9), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (9, -10), (9, -9), (9, -8), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (10, -10), (10, -9), (10, -8), (10, -7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (11, -8), (11, -7), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (12, -7), (12, -6), (12, -5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (13, -5), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (14, -4), (14, -3), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (15, -4), (15, -3), (15, -2), (15, -1), (15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (16, -2), (16, -1), (16, 0), (16, 1), (16, 2), (16, 3), (17, -2), (17, 0), (17, 1), (17, 2), (17, 3)}, 33⟩
theorem entry_614_checked : entryAt 614 = entry_614 := by
  rw [entry_chunk_30 8 (by decide)]
  decide +kernel
theorem row_614 : rowAt 614 = data_614 := by
  rw [rowAt, dif_neg (by decide : ¬ 614 < 6), entry_614_checked]
  change forkRow [placeRow ⟨608, 1, 7, 5⟩ (rowAt 608), placeRow ⟨543, 3, 5, 6⟩ (rowAt 543), placeRow ⟨370, 6, 3, 4⟩ (rowAt 370), placeRow ⟨392, 7, 3, 4⟩ (rowAt 392), placeRow ⟨610, 3, 5, 6⟩ (rowAt 610), placeRow ⟨600, 0, 6, 4⟩ (rowAt 600), placeRow ⟨613, 0, 6, 4⟩ (rowAt 613)] = data_614
  rw [row_608, row_543, row_370, row_392, row_610, row_600, row_613]
  apply row_ext <;> decide +kernel
theorem entry_good_614 : EntryGood 614 := by
  unfold EntryGood
  rw [entry_614_checked]
  decide +kernel
theorem good_614 : Good (rowAt 614) := by
  rw [row_614]
  unfold Good
  decide +kernel

def data_615 : RowData := ⟨{(1, 0)}, {(-15, 0), (-15, 2), (-14, 0), (-14, 1), (-14, 2), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-12, 5), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-10, -9), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6), (-10, 7), (-10, 8), (-10, 9), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7), (-9, 8), (-9, 9), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-8, 7), (-8, 8), (-8, 9), (-8, 10), (-7, -11), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-7, 9), (-7, 10), (-7, 11), (-6, -11), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-5, -12), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-5, 12), (-4, -14), (-4, -13), (-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, -14), (-3, -13), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-3, 14), (-2, -16), (-2, -15), (-2, -14), (-2, -13), (-2, -12), (-2, -11), (-2, -10), (-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16), (-1, -15), (-1, -14), (-1, -13), (-1, -12), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (0, -16), (0, -15), (0, -14), (0, -13), (0, -12), (0, -11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, -15), (1, -14), (1, -13), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (2, -16), (2, -15), (2, -14), (2, -13), (2, -12), (2, -11), (2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (2, 16), (3, -14), (3, -13), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (4, -14), (4, -13), (4, -12), (4, -11), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, -14), (5, -13), (5, -12), (5, -11), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (6, -14), (6, -13), (6, -12), (6, -11), (6, -10), (6, -9), (6, -8), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (7, -12), (7, -11), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, -12), (8, -11), (8, -10), (8, -9), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, -12), (9, -11), (9, -10), (9, -9), (9, -8), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (10, -10), (10, -9), (10, -8), (10, -7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (11, -9), (11, -8), (11, -7), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (12, -9), (12, -8), (12, -7), (12, -6), (12, -5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (13, -6), (13, -5), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (14, -6), (14, -5), (14, -4), (14, -3), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (15, -2), (15, -1), (15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (16, -2), (16, 0), (16, 1), (16, 2), (17, 0), (17, 2)}, 34⟩
theorem entry_615_checked : entryAt 615 = entry_615 := by
  rw [entry_chunk_30 9 (by decide)]
  decide +kernel
theorem row_615 : rowAt 615 = data_615 := by
  rw [rowAt, dif_neg (by decide : ¬ 615 < 6), entry_615_checked]
  change forkRow [placeRow ⟨602, 7, 6, 4⟩ (rowAt 602), placeRow ⟨614, 1, 4, 3⟩ (rowAt 614), placeRow ⟨533, 5, 6, 4⟩ (rowAt 533), placeRow ⟨590, 7, 6, 4⟩ (rowAt 590), placeRow ⟨611, 6, 3, 4⟩ (rowAt 611), placeRow ⟨587, 3, 3, 4⟩ (rowAt 587), placeRow ⟨601, 5, 6, 4⟩ (rowAt 601), placeRow ⟨406, 1, 6, 4⟩ (rowAt 406), placeRow ⟨591, 3, 3, 4⟩ (rowAt 591), placeRow ⟨586, 3, 3, 4⟩ (rowAt 586), placeRow ⟨584, 5, 6, 4⟩ (rowAt 584), placeRow ⟨406, 3, 3, 4⟩ (rowAt 406)] = data_615
  rw [row_602, row_614, row_533, row_590, row_611, row_587, row_601, row_406, row_591, row_586, row_584]
  apply row_ext <;> decide +kernel
theorem entry_good_615 : EntryGood 615 := by
  unfold EntryGood
  rw [entry_615_checked]
  decide +kernel
theorem good_615 : Good (rowAt 615) := by
  rw [row_615]
  unfold Good
  decide +kernel

#check row_615
def indices : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615]
theorem all_good : ∀ i ∈ indices, Good (rowAt i) := by
  simp only [indices, List.forall_mem_cons]
  exact ⟨good_0, good_1, good_2, good_3, good_4, good_5, good_6, good_7, good_8, good_9, good_10, good_11, good_12, good_13, good_14, good_15, good_16, good_17, good_18, good_19, good_20, good_21, good_22, good_23, good_24, good_25, good_26, good_27, good_28, good_29, good_30, good_31, good_32, good_33, good_34, good_35, good_36, good_37, good_38, good_39, good_40, good_41, good_42, good_43, good_44, good_45, good_46, good_47, good_48, good_49, good_50, good_51, good_52, good_53, good_54, good_55, good_56, good_57, good_58, good_59, good_60, good_61, good_62, good_63, good_64, good_65, good_66, good_67, good_68, good_69, good_70, good_71, good_72, good_73, good_74, good_75, good_76, good_77, good_78, good_79, good_80, good_81, good_82, good_83, good_84, good_85, good_86, good_87, good_88, good_89, good_90, good_91, good_92, good_93, good_94, good_95, good_96, good_97, good_98, good_99, good_100, good_101, good_102, good_103, good_104, good_105, good_106, good_107, good_108, good_109, good_110, good_111, good_112, good_113, good_114, good_115, good_116, good_117, good_118, good_119, good_120, good_121, good_122, good_123, good_124, good_125, good_126, good_127, good_128, good_129, good_130, good_131, good_132, good_133, good_134, good_135, good_136, good_137, good_138, good_139, good_140, good_141, good_142, good_143, good_144, good_145, good_146, good_147, good_148, good_149, good_150, good_151, good_152, good_153, good_154, good_155, good_156, good_157, good_158, good_159, good_160, good_161, good_162, good_163, good_164, good_165, good_166, good_167, good_168, good_169, good_170, good_171, good_172, good_173, good_174, good_175, good_176, good_177, good_178, good_179, good_180, good_181, good_182, good_183, good_184, good_185, good_186, good_187, good_188, good_189, good_190, good_191, good_192, good_193, good_194, good_195, good_196, good_197, good_198, good_199, good_200, good_201, good_202, good_203, good_204, good_205, good_206, good_207, good_208, good_209, good_210, good_211, good_212, good_213, good_214, good_215, good_216, good_217, good_218, good_219, good_220, good_221, good_222, good_223, good_224, good_225, good_226, good_227, good_228, good_229, good_230, good_231, good_232, good_233, good_234, good_235, good_236, good_237, good_238, good_239, good_240, good_241, good_242, good_243, good_244, good_245, good_246, good_247, good_248, good_249, good_250, good_251, good_252, good_253, good_254, good_255, good_256, good_257, good_258, good_259, good_260, good_261, good_262, good_263, good_264, good_265, good_266, good_267, good_268, good_269, good_270, good_271, good_272, good_273, good_274, good_275, good_276, good_277, good_278, good_279, good_280, good_281, good_282, good_283, good_284, good_285, good_286, good_287, good_288, good_289, good_290, good_291, good_292, good_293, good_294, good_295, good_296, good_297, good_298, good_299, good_300, good_301, good_302, good_303, good_304, good_305, good_306, good_307, good_308, good_309, good_310, good_311, good_312, good_313, good_314, good_315, good_316, good_317, good_318, good_319, good_320, good_321, good_322, good_323, good_324, good_325, good_326, good_327, good_328, good_329, good_330, good_331, good_332, good_333, good_334, good_335, good_336, good_337, good_338, good_339, good_340, good_341, good_342, good_343, good_344, good_345, good_346, good_347, good_348, good_349, good_350, good_351, good_352, good_353, good_354, good_355, good_356, good_357, good_358, good_359, good_360, good_361, good_362, good_363, good_364, good_365, good_366, good_367, good_368, good_369, good_370, good_371, good_372, good_373, good_374, good_375, good_376, good_377, good_378, good_379, good_380, good_381, good_382, good_383, good_384, good_385, good_386, good_387, good_388, good_389, good_390, good_391, good_392, good_393, good_394, good_395, good_396, good_397, good_398, good_399, good_400, good_401, good_402, good_403, good_404, good_405, good_406, good_407, good_408, good_409, good_410, good_411, good_412, good_413, good_414, good_415, good_416, good_417, good_418, good_419, good_420, good_421, good_422, good_423, good_424, good_425, good_426, good_427, good_428, good_429, good_430, good_431, good_432, good_433, good_434, good_435, good_436, good_437, good_438, good_439, good_440, good_441, good_442, good_443, good_444, good_445, good_446, good_447, good_448, good_449, good_450, good_451, good_452, good_453, good_454, good_455, good_456, good_457, good_458, good_459, good_460, good_461, good_462, good_463, good_464, good_465, good_466, good_467, good_468, good_469, good_470, good_471, good_472, good_473, good_474, good_475, good_476, good_477, good_478, good_479, good_480, good_481, good_482, good_483, good_484, good_485, good_486, good_487, good_488, good_489, good_490, good_491, good_492, good_493, good_494, good_495, good_496, good_497, good_498, good_499, good_500, good_501, good_502, good_503, good_504, good_505, good_506, good_507, good_508, good_509, good_510, good_511, good_512, good_513, good_514, good_515, good_516, good_517, good_518, good_519, good_520, good_521, good_522, good_523, good_524, good_525, good_526, good_527, good_528, good_529, good_530, good_531, good_532, good_533, good_534, good_535, good_536, good_537, good_538, good_539, good_540, good_541, good_542, good_543, good_544, good_545, good_546, good_547, good_548, good_549, good_550, good_551, good_552, good_553, good_554, good_555, good_556, good_557, good_558, good_559, good_560, good_561, good_562, good_563, good_564, good_565, good_566, good_567, good_568, good_569, good_570, good_571, good_572, good_573, good_574, good_575, good_576, good_577, good_578, good_579, good_580, good_581, good_582, good_583, good_584, good_585, good_586, good_587, good_588, good_589, good_590, good_591, good_592, good_593, good_594, good_595, good_596, good_597, good_598, good_599, good_600, good_601, good_602, good_603, good_604, good_605, good_606, good_607, good_608, good_609, good_610, good_611, good_612, good_613, good_614, good_615, by simp⟩

theorem all_rows : AllRows := by
  intro i hi
  apply all_good i
  change i ∈ List.range 616
  exact List.mem_range.mpr hi

def entryIndices : List ℕ := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615]
theorem all_entry_good : ∀ i ∈ entryIndices, EntryGood i := by
  simp only [entryIndices, List.forall_mem_cons]
  exact ⟨entry_good_6, entry_good_7, entry_good_8, entry_good_9, entry_good_10, entry_good_11, entry_good_12, entry_good_13, entry_good_14, entry_good_15, entry_good_16, entry_good_17, entry_good_18, entry_good_19, entry_good_20, entry_good_21, entry_good_22, entry_good_23, entry_good_24, entry_good_25, entry_good_26, entry_good_27, entry_good_28, entry_good_29, entry_good_30, entry_good_31, entry_good_32, entry_good_33, entry_good_34, entry_good_35, entry_good_36, entry_good_37, entry_good_38, entry_good_39, entry_good_40, entry_good_41, entry_good_42, entry_good_43, entry_good_44, entry_good_45, entry_good_46, entry_good_47, entry_good_48, entry_good_49, entry_good_50, entry_good_51, entry_good_52, entry_good_53, entry_good_54, entry_good_55, entry_good_56, entry_good_57, entry_good_58, entry_good_59, entry_good_60, entry_good_61, entry_good_62, entry_good_63, entry_good_64, entry_good_65, entry_good_66, entry_good_67, entry_good_68, entry_good_69, entry_good_70, entry_good_71, entry_good_72, entry_good_73, entry_good_74, entry_good_75, entry_good_76, entry_good_77, entry_good_78, entry_good_79, entry_good_80, entry_good_81, entry_good_82, entry_good_83, entry_good_84, entry_good_85, entry_good_86, entry_good_87, entry_good_88, entry_good_89, entry_good_90, entry_good_91, entry_good_92, entry_good_93, entry_good_94, entry_good_95, entry_good_96, entry_good_97, entry_good_98, entry_good_99, entry_good_100, entry_good_101, entry_good_102, entry_good_103, entry_good_104, entry_good_105, entry_good_106, entry_good_107, entry_good_108, entry_good_109, entry_good_110, entry_good_111, entry_good_112, entry_good_113, entry_good_114, entry_good_115, entry_good_116, entry_good_117, entry_good_118, entry_good_119, entry_good_120, entry_good_121, entry_good_122, entry_good_123, entry_good_124, entry_good_125, entry_good_126, entry_good_127, entry_good_128, entry_good_129, entry_good_130, entry_good_131, entry_good_132, entry_good_133, entry_good_134, entry_good_135, entry_good_136, entry_good_137, entry_good_138, entry_good_139, entry_good_140, entry_good_141, entry_good_142, entry_good_143, entry_good_144, entry_good_145, entry_good_146, entry_good_147, entry_good_148, entry_good_149, entry_good_150, entry_good_151, entry_good_152, entry_good_153, entry_good_154, entry_good_155, entry_good_156, entry_good_157, entry_good_158, entry_good_159, entry_good_160, entry_good_161, entry_good_162, entry_good_163, entry_good_164, entry_good_165, entry_good_166, entry_good_167, entry_good_168, entry_good_169, entry_good_170, entry_good_171, entry_good_172, entry_good_173, entry_good_174, entry_good_175, entry_good_176, entry_good_177, entry_good_178, entry_good_179, entry_good_180, entry_good_181, entry_good_182, entry_good_183, entry_good_184, entry_good_185, entry_good_186, entry_good_187, entry_good_188, entry_good_189, entry_good_190, entry_good_191, entry_good_192, entry_good_193, entry_good_194, entry_good_195, entry_good_196, entry_good_197, entry_good_198, entry_good_199, entry_good_200, entry_good_201, entry_good_202, entry_good_203, entry_good_204, entry_good_205, entry_good_206, entry_good_207, entry_good_208, entry_good_209, entry_good_210, entry_good_211, entry_good_212, entry_good_213, entry_good_214, entry_good_215, entry_good_216, entry_good_217, entry_good_218, entry_good_219, entry_good_220, entry_good_221, entry_good_222, entry_good_223, entry_good_224, entry_good_225, entry_good_226, entry_good_227, entry_good_228, entry_good_229, entry_good_230, entry_good_231, entry_good_232, entry_good_233, entry_good_234, entry_good_235, entry_good_236, entry_good_237, entry_good_238, entry_good_239, entry_good_240, entry_good_241, entry_good_242, entry_good_243, entry_good_244, entry_good_245, entry_good_246, entry_good_247, entry_good_248, entry_good_249, entry_good_250, entry_good_251, entry_good_252, entry_good_253, entry_good_254, entry_good_255, entry_good_256, entry_good_257, entry_good_258, entry_good_259, entry_good_260, entry_good_261, entry_good_262, entry_good_263, entry_good_264, entry_good_265, entry_good_266, entry_good_267, entry_good_268, entry_good_269, entry_good_270, entry_good_271, entry_good_272, entry_good_273, entry_good_274, entry_good_275, entry_good_276, entry_good_277, entry_good_278, entry_good_279, entry_good_280, entry_good_281, entry_good_282, entry_good_283, entry_good_284, entry_good_285, entry_good_286, entry_good_287, entry_good_288, entry_good_289, entry_good_290, entry_good_291, entry_good_292, entry_good_293, entry_good_294, entry_good_295, entry_good_296, entry_good_297, entry_good_298, entry_good_299, entry_good_300, entry_good_301, entry_good_302, entry_good_303, entry_good_304, entry_good_305, entry_good_306, entry_good_307, entry_good_308, entry_good_309, entry_good_310, entry_good_311, entry_good_312, entry_good_313, entry_good_314, entry_good_315, entry_good_316, entry_good_317, entry_good_318, entry_good_319, entry_good_320, entry_good_321, entry_good_322, entry_good_323, entry_good_324, entry_good_325, entry_good_326, entry_good_327, entry_good_328, entry_good_329, entry_good_330, entry_good_331, entry_good_332, entry_good_333, entry_good_334, entry_good_335, entry_good_336, entry_good_337, entry_good_338, entry_good_339, entry_good_340, entry_good_341, entry_good_342, entry_good_343, entry_good_344, entry_good_345, entry_good_346, entry_good_347, entry_good_348, entry_good_349, entry_good_350, entry_good_351, entry_good_352, entry_good_353, entry_good_354, entry_good_355, entry_good_356, entry_good_357, entry_good_358, entry_good_359, entry_good_360, entry_good_361, entry_good_362, entry_good_363, entry_good_364, entry_good_365, entry_good_366, entry_good_367, entry_good_368, entry_good_369, entry_good_370, entry_good_371, entry_good_372, entry_good_373, entry_good_374, entry_good_375, entry_good_376, entry_good_377, entry_good_378, entry_good_379, entry_good_380, entry_good_381, entry_good_382, entry_good_383, entry_good_384, entry_good_385, entry_good_386, entry_good_387, entry_good_388, entry_good_389, entry_good_390, entry_good_391, entry_good_392, entry_good_393, entry_good_394, entry_good_395, entry_good_396, entry_good_397, entry_good_398, entry_good_399, entry_good_400, entry_good_401, entry_good_402, entry_good_403, entry_good_404, entry_good_405, entry_good_406, entry_good_407, entry_good_408, entry_good_409, entry_good_410, entry_good_411, entry_good_412, entry_good_413, entry_good_414, entry_good_415, entry_good_416, entry_good_417, entry_good_418, entry_good_419, entry_good_420, entry_good_421, entry_good_422, entry_good_423, entry_good_424, entry_good_425, entry_good_426, entry_good_427, entry_good_428, entry_good_429, entry_good_430, entry_good_431, entry_good_432, entry_good_433, entry_good_434, entry_good_435, entry_good_436, entry_good_437, entry_good_438, entry_good_439, entry_good_440, entry_good_441, entry_good_442, entry_good_443, entry_good_444, entry_good_445, entry_good_446, entry_good_447, entry_good_448, entry_good_449, entry_good_450, entry_good_451, entry_good_452, entry_good_453, entry_good_454, entry_good_455, entry_good_456, entry_good_457, entry_good_458, entry_good_459, entry_good_460, entry_good_461, entry_good_462, entry_good_463, entry_good_464, entry_good_465, entry_good_466, entry_good_467, entry_good_468, entry_good_469, entry_good_470, entry_good_471, entry_good_472, entry_good_473, entry_good_474, entry_good_475, entry_good_476, entry_good_477, entry_good_478, entry_good_479, entry_good_480, entry_good_481, entry_good_482, entry_good_483, entry_good_484, entry_good_485, entry_good_486, entry_good_487, entry_good_488, entry_good_489, entry_good_490, entry_good_491, entry_good_492, entry_good_493, entry_good_494, entry_good_495, entry_good_496, entry_good_497, entry_good_498, entry_good_499, entry_good_500, entry_good_501, entry_good_502, entry_good_503, entry_good_504, entry_good_505, entry_good_506, entry_good_507, entry_good_508, entry_good_509, entry_good_510, entry_good_511, entry_good_512, entry_good_513, entry_good_514, entry_good_515, entry_good_516, entry_good_517, entry_good_518, entry_good_519, entry_good_520, entry_good_521, entry_good_522, entry_good_523, entry_good_524, entry_good_525, entry_good_526, entry_good_527, entry_good_528, entry_good_529, entry_good_530, entry_good_531, entry_good_532, entry_good_533, entry_good_534, entry_good_535, entry_good_536, entry_good_537, entry_good_538, entry_good_539, entry_good_540, entry_good_541, entry_good_542, entry_good_543, entry_good_544, entry_good_545, entry_good_546, entry_good_547, entry_good_548, entry_good_549, entry_good_550, entry_good_551, entry_good_552, entry_good_553, entry_good_554, entry_good_555, entry_good_556, entry_good_557, entry_good_558, entry_good_559, entry_good_560, entry_good_561, entry_good_562, entry_good_563, entry_good_564, entry_good_565, entry_good_566, entry_good_567, entry_good_568, entry_good_569, entry_good_570, entry_good_571, entry_good_572, entry_good_573, entry_good_574, entry_good_575, entry_good_576, entry_good_577, entry_good_578, entry_good_579, entry_good_580, entry_good_581, entry_good_582, entry_good_583, entry_good_584, entry_good_585, entry_good_586, entry_good_587, entry_good_588, entry_good_589, entry_good_590, entry_good_591, entry_good_592, entry_good_593, entry_good_594, entry_good_595, entry_good_596, entry_good_597, entry_good_598, entry_good_599, entry_good_600, entry_good_601, entry_good_602, entry_good_603, entry_good_604, entry_good_605, entry_good_606, entry_good_607, entry_good_608, entry_good_609, entry_good_610, entry_good_611, entry_good_612, entry_good_613, entry_good_614, entry_good_615, by simp⟩

theorem table_size : table.size = 610 := by decide +kernel
theorem table_valid : TableValid := by
  refine ⟨table_size, ?_⟩
  intro k hk
  have hk610 : k < 610 := by simpa only [table_size] using hk
  have he := all_entry_good (k + 6) (by
    change k + 6 ∈ (List.range 610).map (fun j => j + 6)
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk610, rfl⟩)
  unfold EntryGood at he
  simp only [entryAt, Nat.add_sub_cancel] at he
  refine ⟨he.1, he.2.1, ?_⟩
  intro t ht
  rw [he.1]
  exact he.2.2 t ht

theorem output_557 : Output 557 (-1, 0) 118 19 {p | p.1 ≤ -3 ∧ p.2 ≤ -2} := by
  unfold Output
  rw [row_557]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  apply Set.disjoint_left.mpr
  intro p hp ho
  have safe : ∀ q ∈ data_557.H, ¬ (q.1 ≤ -3 ∧ q.2 ≤ -2) := by decide +kernel
  exact safe p hp ho

theorem output_595 : Output 595 (-1, 0) 222 27 {p | p.1 = -2 ∧ p.2 ≤ -2} := by
  unfold Output
  rw [row_595]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  apply Set.disjoint_left.mpr
  intro p hp ho
  have safe : ∀ q ∈ data_595.H, ¬ (q.1 = -2 ∧ q.2 ≤ -2) := by decide +kernel
  exact safe p hp ho

theorem output_603 : Output 603 (-1, 0) 275 27 {p | p.1 ≤ -3 ∧ p.2 = 0} := by
  unfold Output
  rw [row_603]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  apply Set.disjoint_left.mpr
  intro p hp ho
  have safe : ∀ q ∈ data_603.H, ¬ (q.1 ≤ -3 ∧ q.2 = 0) := by decide +kernel
  exact safe p hp ho

theorem output_615 : Output 615 (1, 0) 686 34 {(1, -1)} := by
  unfold Output
  rw [row_615]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  apply Set.disjoint_left.mpr
  intro p hp ho
  have safe : ∀ q ∈ data_615.H, ¬ (q = (1, -1)) := by decide +kernel
  exact safe p hp ho

theorem certificate_complete :
    TableValid ∧ placementCount = 1837 ∧
    Output 557 (-1, 0) 118 19 {p | p.1 ≤ -3 ∧ p.2 ≤ -2} ∧
    Output 595 (-1, 0) 222 27 {p | p.1 = -2 ∧ p.2 ≤ -2} ∧
    Output 603 (-1, 0) 275 27 {p | p.1 ≤ -3 ∧ p.2 = 0} ∧
    Output 615 (1, 0) 686 34 {(1, -1)} ∧ AllRows := by
  exact ⟨table_valid, by decide +kernel, output_557, output_595,
    output_603, output_615, all_rows⟩

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem solution :
    TableValid ∧ placementCount = 1837 ∧
    Output 557 (-1, 0) 118 19 {p | p.1 ≤ -3 ∧ p.2 ≤ -2} ∧
    Output 595 (-1, 0) 222 27 {p | p.1 = -2 ∧ p.2 ≤ -2} ∧
    Output 603 (-1, 0) 275 27 {p | p.1 ≤ -3 ∧ p.2 = 0} ∧
    Output 615 (1, 0) 686 34 {(1, -1)} ∧ AllRows := by
  exact OAI.SnakyCertificate.MilestoneChecks.certificate_complete

#print axioms OAI.SnakyCertificate.MilestoneChecks.certificate_complete
