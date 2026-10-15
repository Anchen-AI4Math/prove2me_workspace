import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic


namespace OAI.PiExponent.DeterminantContradiction

open Filter
open scoped Topology

theorem logWeights_eq {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) :=
  (d.x_log i.val).symm

end OAI.PiExponent.DeterminantContradiction

namespace OAI.PiExponent.MatrixTranslation

open scoped BigOperators
open MvPolynomial
open RowTranslation

@[simp] theorem card_transverseIndices {m : ℕ} (w : Fin m → ℝ) (H : ℝ) :
    (transverseIndices w H).card = (PiExponent.realWeightedSimplex w H).card := by
  simp [transverseIndices]

end OAI.PiExponent.MatrixTranslation

namespace OAI.PiExponent.RowTranslation

open scoped BigOperators
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem card_bounded_indices_le (a : σ → ℕ) (H : ℕ) (ha : ∀ i, a i ≤ H) :
    Fintype.card (∀ i, Fin (a i + 1)) ≤ (H + 1) ^ Fintype.card σ := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∏ _i : σ, (H + 1) := Finset.prod_le_prod' (fun i hi => Nat.add_le_add_right (ha i) 1)
    _ = _ := by simp

end OAI.PiExponent.RowTranslation

namespace OAI.PiExponent

open scoped BigOperators
open Filter Topology

theorem mem_realWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    rw [mul_comm]
    exact (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
      (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)).trans h

end OAI.PiExponent

namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators
open DeterminantContradiction

theorem fixedWeights_pos {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    0 < fixedWeights d i := by
  change 0 < MatrixArithmetic.logWeights (finiteDenominators d) i
  rw [logWeights_eq]
  exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)

end OAI.PiExponent.LiteralAnalytic

namespace OAI.PiExponent.MatrixTranslation

open scoped BigOperators
open MvPolynomial
open RowTranslation

@[simp] theorem mem_transverseIndices {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 0 < w i) (A : Fin m →₀ ℕ) :
    A ∈ transverseIndices w H ↔ ∑ i, w i * A i ≤ H := by
  classical
  simp only [transverseIndices, Finset.mem_map_equiv, PiExponent.mem_realWeightedSimplex hw]
  rfl

end OAI.PiExponent.MatrixTranslation

namespace OAI.PiExponent.RowTranslation

open scoped BigOperators
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem card_rowChoices_le (S : Finset (σ →₀ ℕ)) (β : σ →₀ ℕ) (s H : ℕ)
    (ha : ∀ a ∈ S, ∀ i, a i ≤ H) :
    Fintype.card (RowChoices S β s) ≤ S.card * (H + 1) ^ Fintype.card σ * (s + 1) := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc
    _ ≤ ∑ _a : S, (H + 1) ^ Fintype.card σ * (s + 1) := by
      apply Finset.sum_le_sum
      intro a ha'
      apply Nat.mul_le_mul_right
      exact card_bounded_indices_le _ H (fun i => (Nat.sub_le _ _).trans (ha a.1 a.2 i))
    _ = _ := by simp [Nat.mul_assoc]

end OAI.PiExponent.RowTranslation

namespace OAI.PiExponent

open scoped BigOperators
open Filter Topology

theorem mem_strictWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ strictWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) < H := by
  classical
  simp only [strictWeightedSimplex, Finset.mem_filter, mem_realWeightedSimplex hw,
    and_iff_right_iff_imp]
  exact fun h => h.le

end OAI.PiExponent

namespace OAI.PiExponent.InterpolationMatrix

open scoped BigOperators

theorem row_mem_iff {m : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (b : Fin (m + 1) → ℕ) :
    b ∈ PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H ↔
      v0 * (b 0 : ℝ) + (∑ i, w i * (b i.succ : ℝ)) / θ < H := by
  have hp : ∀ i, 0 < rowWeights v0 θ w i := by
    intro i
    refine Fin.cases hv0 (fun j => div_pos (hw j) hθ) i
  rw [PiExponent.mem_strictWeightedSimplex hp, Fin.sum_univ_succ]
  simp only [rowWeights, Fin.cases_zero, Fin.cases_succ, div_mul_eq_mul_div,
    Finset.sum_div]

end OAI.PiExponent.InterpolationMatrix

namespace OAI.PiExponent.MatrixTranslation

open scoped BigOperators
open MvPolynomial
open RowTranslation

theorem transverseIndices_coordinate_le {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 1 ≤ w i) {A : Fin m →₀ ℕ} (hA : A ∈ transverseIndices w H) (i : Fin m) :
    A i ≤ ⌊H⌋₊ := by
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le zero_lt_one (hw i)
  have ha := (mem_transverseIndices w H hwpos A).mp hA
  apply Nat.le_floor
  calc
    (A i : ℝ) ≤ w i * A i := by nlinarith [show (0 : ℝ) ≤ (A i : ℝ) by positivity, hw i]
    _ ≤ ∑ k, w k * A k := Finset.single_le_sum
      (fun k hk => mul_nonneg (hwpos k).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
    _ ≤ H := ha

end OAI.PiExponent.MatrixTranslation

namespace OAI.PiExponent.RowTranslation

open scoped BigOperators
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem card_rowChoices_box_le (S : Finset (σ →₀ ℕ)) (β : σ →₀ ℕ) (s H : ℕ)
    (ha : ∀ a ∈ S, ∀ i, a i ≤ H)
    (hS : S.card ≤ (H + 1) ^ Fintype.card σ) :
    Fintype.card (RowChoices S β s) ≤ (H + 1) ^ (2 * Fintype.card σ) * (s + 1) := by
  calc
    _ ≤ S.card * (H + 1) ^ Fintype.card σ * (s + 1) := card_rowChoices_le S β s H ha
    _ ≤ (H + 1) ^ Fintype.card σ * (H + 1) ^ Fintype.card σ * (s + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hS)
    _ = _ := by rw [← pow_add]; congr 2; omega

end OAI.PiExponent.RowTranslation

namespace OAI.PiExponent.InterpolationMatrix

open scoped BigOperators

theorem row_weight_lt {m K : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (ρ : Row K v0 θ w H) :
    v0 * (ρ.2.1 0 : ℝ) + (∑ i, w i * (ρ.2.1 i.succ : ℝ)) / θ < H :=
  (row_mem_iff hv0 hθ hw ρ.2.1).mp ρ.2.2

end OAI.PiExponent.InterpolationMatrix

namespace OAI.PiExponent.MatrixTranslation

open scoped BigOperators
open MvPolynomial
open RowTranslation

theorem transverseIndices_card_le {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 1 ≤ w i) :
    (transverseIndices w H).card ≤ (⌊H⌋₊ + 1) ^ m := by
  classical
  let box : Finset (Fin m → ℕ) := Fintype.piFinset (fun _ => Finset.range (⌊H⌋₊ + 1))
  have hcard : (transverseIndices w H).card ≤ box.card := by
    apply Finset.card_le_card_of_injOn (fun A : Fin m →₀ ℕ => fun i => A i)
    · intro A hA
      apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (transverseIndices_coordinate_le w H hw hA i))
    · intro A hA B hB he
      exact Finsupp.ext (fun i => congrFun he i)
  simpa [box, Fintype.card_piFinset] using hcard

end OAI.PiExponent.MatrixTranslation

namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators
open DeterminantContradiction

theorem rowOrder_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) :
    (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) := by
  have hr := InterpolationMatrix.row_weight_lt d.v0_pos d.base.theta_pos (fixedWeights_pos d) r
  have hs : 0 ≤ (∑ i, fixedWeights d i * (r.2.1 i.succ : ℝ)) / (d.base.theta : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (fixedWeights_pos d i).le (Nat.cast_nonneg _))
      d.base.theta_pos.le
  apply (le_div_iff₀ d.v0_pos).mpr
  nlinarith

end OAI.PiExponent.LiteralAnalytic

namespace OAI.PiExponent.MatrixTranslation

open scoped BigOperators
open MvPolynomial
open RowTranslation

theorem row_term_count {m : ℕ} (w : Fin m → ℝ) (H v : ℝ)
    (hw : ∀ i, 1 ≤ w i) (β : Fin m →₀ ℕ) (s : ℕ) (hs : (s : ℝ) ≤ H / v) :
    Fintype.card (RowChoices (transverseIndices w H) β s) ≤
      (⌊H⌋₊ + 1) ^ (2 * m) * (⌊H / v⌋₊ + 1) := by
  have h := card_rowChoices_box_le (transverseIndices w H) β s ⌊H⌋₊
    (fun A hA i => transverseIndices_coordinate_le w H hw hA i)
    (by simpa using transverseIndices_card_le w H hw)
  simp only [Fintype.card_fin] at h
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.le_floor hs) 1))

end OAI.PiExponent.MatrixTranslation
theorem solution {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    Fintype.card (ChoiceFamily d H) ≤ translationTermCount d.m d.v0 H ^ actualRowCount d H := by
  classical
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _r : Row d H, translationTermCount d.m d.v0 H := by
      apply Finset.prod_le_prod'
      intro r _
      exact MatrixTranslation.row_term_count (fixedWeights d) H d.v0
        (fun i => by change 1 ≤ MatrixArithmetic.logWeights (finiteDenominators d) i
                     rw [logWeights_eq]; exact d.x_one_le _)
        (beta d r) (r.2.1 0) (rowOrder_le d r)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, actualRowCount]
