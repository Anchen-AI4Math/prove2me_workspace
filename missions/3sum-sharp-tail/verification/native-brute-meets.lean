import Mathlib
import Definitions.Def_APSP299791_Defs5

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Nat

theorem mul_add_le_mul {a b c : ℕ} (hab : a < b) (_ : c ≤ c) : a * c + c ≤ b * c := by
  have h := Nat.mul_le_mul_right c (Nat.succ_le_of_lt hab)
  simpa [Nat.succ_mul] using h

end Nat

namespace ThreeSumApsp

theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · have hlen : l.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getD_eq_default _ _ hlen]
    exact hU

end ThreeSumApsp

namespace Light

theorem Seg.of_sameOutside {μ μ' : ℕ → ℤ} {b a n : ℕ} {l : List ℤ}
    (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l := by
  intro i hi
  rw [hs _ (by omega)]
  exact h i hi

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩

theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q := ⟨_, _, .store ha he hA, hT, h⟩

theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩

theorem Ends.while {σ c s} {Q : State → Prop} (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    Ends lim P d (.while c s) σ
      (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by
  have aux : ∀ j i σ, i + j = n → I i σ →
      Ends lim P d (.while c s) σ
        (∑ k ∈ Finset.range j, (c.cost + 1 + b (i + k)) + (c.cost + 1)) Q := by
    intro j
    induction j with
    | zero =>
      intro i σ hij hi
      obtain rfl : i = n := by omega
      obtain ⟨h1, h2, h3⟩ := hn σ hi
      exact ⟨σ, _, .whileFalse h1 h2, by simp, h3⟩
    | succ j ih =>
      intro i σ hij hi
      obtain ⟨h1, h2, σ', k₁, he₁, hk₁, hi'⟩ := hs i σ (by omega) hi
      obtain ⟨σ'', k₂, he₂, hk₂, hq⟩ := ih (i + 1) σ' (by omega) hi'
      refine ⟨σ'', _, .whileTrue h1 h2 he₁ he₂, ?_, hq⟩
      rw [Finset.sum_range_succ']
      have : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
      simp only [this] at hk₂
      simp only [Nat.add_zero]
      omega
  simpa using aux n 0 σ (by omega) hI

theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h

theorem Ends.of_blockSafe : ∀ {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop},
    s.BlockSafe lim σ → s.blockCost ≤ T → Q (s.after σ) → Ends lim P d s σ T Q
  | .skip, _, _, _, _, _, h => Ends.skip h
  | .set _ _, _, _, _, hs, hT, h => Ends.set hs hT h
  | .store _ _, _, _, _, hs, hT, h => Ends.store hs.1 hs.2.1 hs.2.2 hT h
  | .seq s t, _, _, _, hs, hT, h =>
    Ends.seq s.blockCost t.blockCost
      (Ends.of_blockSafe hs.1 le_rfl (Ends.of_blockSafe hs.2 le_rfl h)) hT
  | .ite c s t, σ, _, _, hs, hT, h =>
    Ends.ite (max s.blockCost t.blockCost) hs.1
      (fun hc => Ends.of_blockSafe (hs.2.1 hc) (le_max_left _ _)
        (by simpa only [Stmt.after, if_pos hc] using h))
      (fun hc => Ends.of_blockSafe (hs.2.2 hc) (le_max_right _ _)
        (by simpa only [Stmt.after, if_neg hc] using h)) hT
  | .while _ _, _, _, _, hs, _, _ => hs.elim
  | .call _ _ _, _, _, _, hs, _, _ => hs.elim

theorem Ends.block {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : s.Runs lim σ Q) (hT : s.blockCost ≤ T) : Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2

theorem Ends.whileBlock {σ : State} {c : Cond} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (start : I 0 σ)
    (round : ∀ (j : ℕ) (σ : State), j < n → I j σ →
      c.Safe lim σ ∧ c.Holds σ ∧ body.Runs lim σ (I (j + 1)))
    (done : ∀ σ : State, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + body.blockCost) + (c.cost + 1) ≤ T := by
      simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      first | omega | (ring_nf; omega)) :
    Ends lim P d (.while c body) σ T Q :=
  Ends.whileConst I n body.blockCost start
    (fun j σ hj hI => ⟨(round j σ hj hI).1, (round j σ hj hI).2.1,
      Ends.block (round j σ hj hI).2.2 le_rfl⟩) done hT

theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s ;; .skip) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ => cases he₂; exact ⟨σ', _, he₁, by omega, hq⟩

theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by
      simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      first | omega | (ring_nf; omega)) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; (s₂ ;; s₃)) σ T Q) : Ends lim P d ((s₁ ;; s₂) ;; s₃) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) : Ends lim P d (.skip ;; s) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; s₂) σ T Q) : Ends lim P d (s₁ ;; s₂) σ T Q := h

theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]

theorem Ends.setToThen {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}
    {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z) (hT : e.cost + 1 ≤ T) :
    Ends lim P d (.set x e ;; s) ⟨frame l, μ⟩ T Q := by
  refine Ends.next _ (Ends.set he.1 le_rfl ?_) hT
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

theorem Ends.storeToThen {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}
    {a e : Expr} {s : Stmt} (b : ℕ) (z : ℤ)
    (h : Ends lim P d s ⟨frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space)
    (hT : a.cost + e.cost + 1 ≤ T) : Ends lim P d (.store a e ;; s) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he', hev⟩, hb⟩ := he
  refine Ends.next _ (Ends.store ha he' ?_ le_rfl ?_) hT
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

end Light

namespace Light

theorem SameOutside.refl {μ : ℕ → ℤ} {a n : ℕ} : SameOutside μ μ a n := by
  intro b hb
  rfl

theorem frame_append_zeros (l : List ℤ) (n : ℕ) :
    frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

end Light

section
-- Source module: ThreeSumApsp.Programs.Sec2.Theorem5.Instance
@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {x : ThinInst} {m : ℕ} {μ : ℕ → ℤ} {fr : ℕ}

section positions

variable {i : ℕ}

/-- A number of a wanted position is an index of the list of the rows. -/
theorem _root_.Light.ThinInst.Pre.lt_lenWI (hpre : x.Pre μ fr) (hi : i < x.w) : i < x.WI.length :=
  hi.trans_eq hpre.lenWI.symm

/-- A number of a wanted position is an index of the list of the columns. -/
theorem _root_.Light.ThinInst.Pre.lt_lenWJ (hpre : x.Pre μ fr) (hi : i < x.w) : i < x.WJ.length :=
  hi.trans_eq hpre.lenWJ.symm

/-- A number of a wanted position is an index of the list of the positions. -/
theorem _root_.Light.ThinInst.Pre.lt_lenZip (hpre : x.Pre μ fr) (hi : i < x.w) :
    i < (x.WI.zip x.WJ).length := by
  simp [hpre.lenWI, hpre.lenWJ, hi]

theorem thinI_eq (h : i < x.WI.length) : thinI x i = x.WI[i] := List.getD_eq_getElem _ _ h

theorem thinJ_eq (h : i < x.WJ.length) : thinJ x i = x.WJ[i] := List.getD_eq_getElem _ _ h

/-- The rows of the wanted positions are rows of the matrix. -/
theorem thinI_lt (hpre : x.Pre μ fr) (hi : i < x.w) : thinI x i < x.N := by
  rw [thinI_eq (hpre.lt_lenWI hi)]
  exact hpre.ltWI _ (List.getElem_mem _)

/-- The columns of the wanted positions are columns of the matrix. -/
theorem thinJ_lt (hpre : x.Pre μ fr) (hi : i < x.w) : thinJ x i < x.N := by
  rw [thinJ_eq (hpre.lt_lenWJ hi)]
  exact hpre.ltWJ _ (List.getElem_mem _)

/-- The rows of the wanted positions, in the memory. -/
theorem mem_thinI (hpre : x.Pre μ fr) (hi : i < x.w) : μ (x.wi + i) = (thinI x i : ℕ) := by
  rw [thinI_eq (hpre.lt_lenWI hi), hpre.segWI i (by simpa using hpre.lt_lenWI hi),
    List.getElem_map]

/-- The columns of the wanted positions, in the memory. -/
theorem mem_thinJ (hpre : x.Pre μ fr) (hi : i < x.w) : μ (x.wj + i) = (thinJ x i : ℕ) := by
  rw [thinJ_eq (hpre.lt_lenWJ hi), hpre.segWJ i (by simpa using hpre.lt_lenWJ hi),
    List.getElem_map]

end positions

/-- There is one answer for each wanted position. -/
theorem length_thinOut (hpre : x.Pre μ fr) : (thinOut x.N x.D x.X x.Y x.WI x.WJ).length = x.w := by
  simp [thinOut, hpre.lenWI, hpre.lenWJ]

/-- The answer number i. -/
theorem getD_thinOut (hpre : x.Pre μ fr) {i : ℕ} (hi : i < x.w) :
    (thinOut x.N x.D x.X x.Y x.WI x.WJ).getD i 0
      = thinEntry x.N x.D x.X x.Y (thinI x i) (thinJ x i) := by
  rw [thinI_eq (hpre.lt_lenWI hi), thinJ_eq (hpre.lt_lenWJ hi)]
  unfold thinOut
  rw [List.getD_eq_getElem _ _ (by simpa using hpre.lt_lenZip hi), List.getElem_map,
    List.getElem_zip]

end Light.Sec2
end
end

section
-- Source module: ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.BruteForce
@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Brute

end Brute

open ThinArg Brute

/-- One more term. -/
theorem brutePartial_succ (N D : ℕ) (X Y : List ℤ) (I J n : ℕ) :
    brutePartial N D X Y I J (n + 1)
      = brutePartial N D X Y I J n + X.getD (I * D + n) 0 * Y.getD (n * N + J) 0 := by
  simp [brutePartial, List.range_succ]

/-- A term of the inner product is at most U². -/
theorem abs_bruteTerm_le {X Y : List ℤ} {U : ℕ} (hX : AbsLe X U) (hY : AbsLe Y U) (a b : ℕ) :
    |X.getD a 0 * Y.getD b 0| ≤ (U * U : ℕ) := by
  rw [abs_mul]
  push_cast
  exact mul_le_mul (hX.abs_getD_le (by positivity) a) (hY.abs_getD_le (by positivity) b)
    (abs_nonneg _) (by positivity)

/-- The first n terms add up to at most n U². -/
theorem abs_brutePartial_le {N D : ℕ} {X Y : List ℤ} {U : ℕ} (hX : AbsLe X U) (hY : AbsLe Y U)
    (I J n : ℕ) : |brutePartial N D X Y I J n| ≤ n * (U * U : ℕ) := by
  induction n with
  | zero => simp [brutePartial]
  | succ n ih =>
    rw [brutePartial_succ]
    calc |brutePartial N D X Y I J n + X.getD (I * D + n) 0 * Y.getD (n * N + J) 0|
        ≤ |brutePartial N D X Y I J n| + |X.getD (I * D + n) 0 * Y.getD (n * N + J) 0| :=
          abs_add_le _ _
      _ ≤ n * (U * U : ℕ) + (U * U : ℕ) := add_le_add ih (abs_bruteTerm_le hX hY _ _)
      _ = ((n + 1 : ℕ) : ℤ) * (U * U : ℕ) := by push_cast; ring

/-- **The inner product** of row I of X and column J of Y. -/
theorem bruteInner_spec (std : Std lim) (x : ThinInst) {μ : ℕ → ℤ} {fr i I J : ℕ} {u : ℤ}
    (segX : Seg μ x.x x.X) (segY : Seg μ x.y x.Y) (lX : x.X.length = x.N * x.D)
    (lY : x.Y.length = x.D * x.N) (bX : AbsLe x.X x.U) (bY : AbsLe x.Y x.U) (hI : I < x.N)
    (hJ : J < x.N) (roomX : x.x + x.N * x.D < lim.space) (roomY : x.y + x.D * x.N + x.N < lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d Light.Sec2.bruteInner ⟨Light.frame (bruteLocs x u fr i 0 (x.x + I * x.D) (x.y + J) 0), μ⟩
      (24 * x.D + 4) fun σ' => σ' = ⟨Light.frame (bruteLocs x u fr i x.D (x.x + I * x.D + x.D)
        (x.y + x.D * x.N + J) (brutePartial x.N x.D x.X x.Y I J x.D)), μ⟩ := by
  have hw := std.space_le
  have h100 := std.const_le
  have hID := Nat.mul_add_le_mul hI (le_refl x.D)
  unfold Light.Sec2.bruteInner
  refine Ends.whileBlock (σ := ⟨Light.frame (bruteLocs x u fr i 0 (x.x + I * x.D) (x.y + J) 0), μ⟩)
    (fun t σ => σ = ⟨Light.frame (bruteLocs x u fr i t (x.x + I * x.D + t)
    (x.y + t * x.N + J) (brutePartial x.N x.D x.X x.Y I J t)), μ⟩) x.D
    (by simp [brutePartial]) ?round ?done
  case round =>
    rintro t _ ht rfl
    have htN := Nat.mul_add_le_mul ht (le_refl x.N)
    have rX : μ (x.x + I * x.D + t) = x.X.getD (I * x.D + t) 0 := by
      rw [Nat.add_assoc]
      exact segX.getD (by omega) 0
    have rY : μ (x.y + t * x.N + J) = x.Y.getD (t * x.N + J) 0 := by
      rw [Nat.add_assoc]
      exact segY.getD (by omega) 0
    have hmono : ∀ n ≤ x.D, ((n : ℤ) * (x.U * x.U : ℕ)) ≤ lim.word := fun n hn =>
      le_trans (by exact_mod_cast Nat.mul_le_mul_right (x.U * x.U) hn) hword
    have hsum := abs_le.mp ((abs_brutePartial_le (N := x.N) (D := x.D) bX bY I J (t + 1)).trans
      (by exact_mod_cast hmono (t + 1) (by omega)))
    have hterm := abs_le.mp ((abs_bruteTerm_le bX bY (I * x.D + t) (t * x.N + J)).trans
      (by simpa using hmono 1 (by omega)))
    have hnext := brutePartial_succ x.N x.D x.X x.Y I J t
    rw [hnext] at hsum
    generalize x.X.getD (I * x.D + t) 0 = a, x.Y.getD (t * x.N + J) 0 = b at *
    generalize hpx : x.x + I * x.D + t = px at *
    generalize hpy : x.y + t * x.N + J = py at *
    have hpx' : (px : ℤ) + 1 = x.x + I * x.D + (t + 1) := by rw [← hpx]; push_cast; ring
    have hpy' : (py : ℤ) + x.N = x.y + (t + 1) * x.N + J := by rw [← hpy]; push_cast; ring
    exact ⟨by simp, by simp [bruteLocs]; omega,
      by (( (try have := Light.Std.space_le (by assumption))
            (try have := Light.Std.const_le (by assumption))
            (simp [Light.Limits.Addr, abs_le, -abs_mul, bruteLocs, rX, rY] <;> omega))),
      by simp [bruteLocs, update_frame_setLocal, rX, rY, hnext, hpx', hpy']⟩
  case done =>
    rintro _ rfl
    exact ⟨by simp, by simp [bruteLocs], rfl⟩

/-- **One wanted position.** -/
theorem bruteRound_spec (std : Std lim) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} {u : ℤ}
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) {i : ℕ} (hi : i < x.w) {σ : State}
    (h : BruteInv x μ u fr i σ) :
    Ends lim P d bruteRound σ (24 * x.D + 33) (BruteInv x μ u fr (i + 1)) := by
  obtain ⟨t, px, py, s, μ', rfl, hdone, hfr⟩ := h
  have hw := std.space_le
  have h100 := std.const_le
  have hbelow := And.intro hpre.belowX (And.intro hpre.belowY (And.intro hpre.belowWI
    (And.intro hpre.belowWJ hpre.belowOut)))
  have hI := thinI_lt hpre hi
  have hJ := thinJ_lt hpre hi
  have segX : Seg μ' x.x x.X :=
    hpre.segX.of_sameOutside hfr (by rw [hpre.lenX]; exact hpre.apartX.symm)
  have segY : Seg μ' x.y x.Y :=
    hpre.segY.of_sameOutside hfr (by rw [hpre.lenY]; exact hpre.apartY.symm)
  have rI : μ' (x.wi + i) = (thinI x i : ℕ) := by
    rw [hfr _ (by rcases hpre.apartWI with h | h <;> omega)]
    exact mem_thinI hpre hi
  have rJ : μ' (x.wj + i) = (thinJ x i : ℕ) := by
    rw [hfr _ (by rcases hpre.apartWJ with h | h <;> omega)]
    exact mem_thinJ hpre hi
  have hidxI : ((x.wi : ℤ) + (i : ℤ)).toNat = x.wi + i := by
    push_cast
    omega
  have hidxJ : ((x.wj : ℤ) + (i : ℤ)).toNat = x.wj + i := by
    push_cast
    omega
  have rIcast : μ' (((x.wi : ℤ) + (i : ℤ)).toNat) = (thinI x i : ℤ) := by
    rw [hidxI, rI]
  have rJcast : μ' (((x.wj : ℤ) + (i : ℤ)).toNat) = (thinJ x i : ℤ) := by
    rw [hidxJ, rJ]
  have hID := Nat.mul_add_le_mul hI (le_refl x.D)
  have hND : x.N ≤ x.D * x.N := Nat.le_mul_of_pos_left _ hpre.D_pos
  unfold bruteRound bruteLocs
  -- t := 0; px := x + mem[wi + i] * D; py := y + mem[wj + i]; s := 0
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine Light.Ends.setToThen 0 ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, ])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
         try have := Light.Std.space_le (by assumption)
         try have := Light.Std.const_le (by assumption)
         simp [Light.Limits.Addr, abs_le, -abs_mul] <;> omega)
     (try with_unfolding_none refine Light.Ends.skip ?_))
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine Light.Ends.setToThen (x.x + thinI x i * x.D : ℕ) ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, rIcast])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
            (simp [rIcast] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
         try have := Light.Std.space_le (by assumption)
         try have := Light.Std.const_le (by assumption)
         simp [Light.Limits.Addr, abs_le, -abs_mul, rIcast] <;> omega)
     (try with_unfolding_none refine Light.Ends.skip ?_))
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine Light.Ends.setToThen (x.y + thinJ x i : ℕ) ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, rJcast])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
            (simp [rJcast] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
          try have := Light.Std.space_le (by assumption)
          try have := Light.Std.const_le (by assumption)
          simp [Light.Limits.Addr, abs_le, -abs_mul, rJcast] <;> omega)
     (try with_unfolding_none refine Light.Ends.skip ?_))
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine
         Light.Ends.setToThen
           0
             -- the inner product
             
           ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, ])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
          try have := Light.Std.space_le (by assumption)
          try have := Light.Std.const_le (by assumption)
          simp [Light.Limits.Addr, abs_le, -abs_mul] <;> omega)
     (try with_unfolding_none refine Light.Ends.skip ?_))
  -- the inner product
  refine Ends.next (24 * x.D + 4) ((bruteInner_spec std x (i := i) segX segY hpre.lenX hpre.lenY
    hpre.leX hpre.leY hI hJ (by omega) (by omega) hword).mono le_rfl ?_)
  rintro _ rfl
  unfold bruteLocs
  -- mem[out + i] := s; i := i + 1
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine
         Light.Ends.storeToThen (x.out + i) (brutePartial x.N x.D x.X x.Y (thinI x i) (thinJ x i) x.D)
           ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, ])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
         try have := Light.Std.space_le (by assumption)
         try have := Light.Std.const_le (by assumption)
         simp [Light.Limits.Addr, abs_le, -abs_mul] <;> omega)
     (try with_unfolding_none refine Light.Ends.skip ?_))
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine Light.Ends.setToThen (i + 1 : ℕ) ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, ])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
         try have := Light.Std.space_le (by assumption)
         try have := Light.Std.const_le (by assumption)
         simp [Light.Limits.Addr, abs_le, -abs_mul] <;> omega)
     (try with_unfolding_none refine Light.Ends.skip ?_))
  refine ⟨_, _, _, _, _, rfl, fun j hj => ?_, ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
  · rw [Function.update_of_ne (by omega)]
    exact hdone j hlt
  · rw [Function.update_self]
    rfl
  · intro a ha
    change Function.update μ' (x.out + i) _ a = μ a
    rw [Function.update_of_ne (by
      intro heq
      rcases ha with hlt | hge <;> omega)]
    exact hfr a (by rcases ha with hlt | hge <;> omega)

/-- **The brute force is right on every instance** for which D U² fits in a word.  It needs N + 1
cells above the free pointer only as room for addresses that are formed and never used. -/
theorem thinBrute_spec (std : Std lim) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (u : ℤ)
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d thinBruteBody
      ⟨Light.frame [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), u, (x.x : ℤ), (x.y : ℤ), (x.wi : ℤ), (x.wj : ℤ),
        (x.out : ℤ), (fr : ℤ)], μ⟩
      (40 * ((x.w + 1) * (x.D + 1))) fun σ' => thinTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  unfold thinBruteBody
  refine Ends.whileConst (BruteInv x μ u fr) x.w (24 * x.D + 33) ?start ?round ?done ?time
  case start =>
    exact ⟨0, 0, 0, 0, μ, by rw [← frame_append_zeros _ 5]; rfl, fun j hj => absurd hj (by omega),
      SameOutside.refl⟩
  case round =>
    intro i σ hi h
    refine ⟨?_, ?_, bruteRound_spec std hpre hsp hword hi h⟩ <;>
      obtain ⟨t, px, py, s, μ', rfl, -, -⟩ := h
    · simp
    · simpa [bruteLocs] using hi
  case done =>
    rintro _ ⟨t, px, py, s, μ', rfl, hdone, hfr⟩
    refine ⟨by simp, by simp [bruteLocs], fun i hi => ?_, fun a ha => hfr a ha.2⟩
    have hi' : i < x.w := by rwa [Light.Sec2.length_thinOut hpre] at hi
    change μ' (x.out + i) = _
    rw [hdone i hi', ← getD_thinOut hpre hi', List.getD_eq_getElem _ _ hi]
  case time =>
    have hleft : x.w * (4 + (24 * x.D + 33)) = 24 * (x.w * x.D) + 37 * x.w := by ring
    have hright : (x.w + 1) * (x.D + 1) = x.w * x.D + x.w + x.D + 1 := by ring
    simp
    omega

end Light.Sec2
end
end


namespace Light.Sec4
open ThreeSumApsp

theorem pruned_program_thinBrute_lookup (G : RatParams) :
    (program31P G)[Sec2.pThinBrute]? = some Sec2.thinBruteBody := by rfl

theorem pruned_program_thinBrute_meets (G : RatParams) (R : Program)
    (lim : Limits) (d : ℕ) (std : Std lim)
    (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim (program31P G ++ R) Sec2.pThinBrute (d + 1)
      [x.N,x.D,x.w,x.U,x.x,x.y,x.wi,x.wj,x.out,fr] μ
      (40 * ((x.w + 1) * (x.D + 1)))
      (fun r μ' => lopCountTask.Post x μ fr r μ') := by
  refine ⟨Sec2.thinBruteBody, ?_, ?_⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp (pruned_program_thinBrute_lookup G)).1]
    exact pruned_program_thinBrute_lookup G
  · exact Sec2.thinBrute_spec std x μ fr x.U hpre hsp hword

end Light.Sec4
#print axioms Light.Sec4.pruned_program_thinBrute_meets
