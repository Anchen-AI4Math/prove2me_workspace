import Definitions.Def_SnakyCertificate
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


end OAI.SnakyCertificate.MilestoneChecks
