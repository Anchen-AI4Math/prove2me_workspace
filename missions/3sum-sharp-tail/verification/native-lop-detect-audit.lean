/- Audit of the generic lop-count to lop-detect wrapper. -/
import Definitions.Def_APSP299791_Defs5
import Theorems.Thm_ThreeSumSharpTail_pruned_program_solves
import Theorems.Thm_ThreeSumSharpTail_rational_power_representation
import Theorems.Thm_ThreeSumSharpTail_pruned_program_correct
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Light
variable {lim : Limits} {P : Program} {d : ℕ} {l : List ℤ} {μ : ℕ → ℤ}
  {T : ℕ} {Q : State → Prop}
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt}
    (h : P[p]? = some body) (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q)
    (hT : T₁ + T₂ ≤ T) : Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

theorem Ends.while {σ c s} {Q : State → Prop} (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    Ends lim P d (.while c s) σ (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by
  have aux : ∀ j i σ, i + j = n → I i σ →
      Ends lim P d (.while c s) σ
        (∑ k ∈ Finset.range j, (c.cost + 1 + b (i + k)) + (c.cost + 1)) Q := by
    intro j
    induction j with
    | zero =>
      intro i σ hij hi
      have hEq : i = n := by omega
      subst i
      obtain ⟨h1, h2, h3⟩ := hn σ hi
      exact ⟨σ, _, .whileFalse h1 h2, by simp, h3⟩
    | succ j ih =>
      intro i σ hij hi
      obtain ⟨h1, h2, σ', k₁, he₁, hk₁, hi'⟩ := hs i σ (by omega) hi
      obtain ⟨σ'', k₂, he₂, hk₂, hq⟩ := ih (i + 1) σ' (by omega) hi'
      refine ⟨σ'', _, .whileTrue h1 h2 he₁ he₂, ?_, hq⟩
      rw [Finset.sum_range_succ']
      have hshift : ∀ k, i + 1 + k = i + (k + 1) := by intro k; omega
      simp only [hshift] at hk₂
      simp only [Nat.add_zero]
      omega
  simpa using aux n 0 σ (by omega) hI

theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q := by
  obtain ⟨σ', c', he, hc, hq⟩ := Ends.while I n (fun _ => b) hI hs hn
  exact ⟨σ', c', he, by
    have hsum : (∑ i ∈ Finset.range n, (c.cost + 1 + b) + (c.cost + 1)) =
        n * (c.cost + 1 + b) + (c.cost + 1) := by simp [Finset.sum_const, Nat.mul_comm]
    rw [hsum] at hc
    exact hc.trans hT, hq⟩

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

theorem wrote_zero {μ : ℕ → ℤ} {dst : ℕ} {f : ℕ → ℤ} : wrote μ dst f 0 = μ := by
  funext a
  unfold wrote
  rw [if_neg (by omega)]

theorem wrote_done {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ} {i : ℕ} (h : i < j) :
    wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

theorem wrote_rest {μ : ℕ → ℤ} {dst j a : ℕ} {f : ℕ → ℤ} (h : Outside dst j a) :
    wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]

theorem wrote_succ {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ} :
    Function.update (wrote μ dst f j) (dst + j) (f j) = wrote μ dst f (j + 1) := by
  funext a
  by_cases h : a = dst + j
  · subst h
    rw [Function.update_self, wrote_done (Nat.lt_succ_self j)]
  · rw [Function.update_of_ne h]
    unfold wrote
    by_cases h' : dst ≤ a ∧ a < dst + j
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]

theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) :
    Ends lim P d (.set x e) σ T Q := ⟨_, _, .set hs, hT, h⟩

theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ)
    (ha : ∀ e ∈ args, e.Safe lim σ) (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) :
    Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩

theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by
      have := Light.Std.space_le (by assumption)
      have := Light.Std.const_le (by assumption)
      simp [Light.Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hT : c.cost + 1 ≤ T := by simp [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost] <;> omega) :
    Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩

theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q := ⟨_, _, .store ha he hA, hT, h⟩

theorem Ends.storeTo {a e : Expr} (b : ℕ) (z : ℤ)
    (h : Q ⟨frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      have := Light.Std.space_le (by assumption)
      have := Light.Std.const_le (by assumption)
      simp [Light.Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hT : a.cost + e.cost + 1 ≤ T := by simp [Light.Stmt.blockCost, Light.Expr.cost] <;> omega) :
    Ends lim P d (.store a e) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he', hev⟩, hb⟩ := he
  refine Ends.store ha he' ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ →
      Ends lim P d body σ b fun σ' =>
        σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ →
      hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (n * (hi.cost + b + 7) + hi.cost + 3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine Ends.whileConst (fun j σ => σ.loc i = j ∧ I j σ) n (b + 4)
    ⟨by simp, by simpa using start⟩ ?_ ?_ (le_of_eq (by simp only [Cond.cost, Expr.cost]; ring))
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq b 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : (((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _

theorem Ends.forMem {loc : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ}
    {Q : State → Prop} (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨Function.update loc i j, μ'⟩ b fun σ' =>
        σ'.loc = Function.update loc i j ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨Function.update loc i n, μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Safe lim ⟨Function.update loc i j, μ'⟩ ∧ hi.val ⟨Function.update loc i j, μ'⟩ = n)
    (hn : (n : ℤ) ≤ lim.word)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T) :
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ => σ.loc = Function.update loc i j ∧ I j σ.mem) n b
    ⟨by simp, start⟩ ?_ ?_ ?_ hn hT
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    refine (round j μ' hj hI).mono le_rfl ?_
    rintro ⟨_, μ''⟩ ⟨rfl, hI'⟩
    exact ⟨by simp, by simp, hI'⟩
  · rintro ⟨_, μ'⟩ - ⟨rfl, hI⟩
    exact done μ' hI
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    exact bound j μ' hj hI

theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T) : Ends lim P d (Light.Stmt.seq s₁ s₂) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

theorem Ends.forFrame {i : ℕ} {hi : Expr} {body : Stmt} (I : ℕ → (ℕ → ℤ) → Prop) (n : ℕ)
    (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨frame (setLocal l i j), μ'⟩ body.blockCost fun σ' =>
        σ'.loc = frame (setLocal l i j) ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal l i n), μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Gives lim ⟨frame (setLocal l i j), μ'⟩ n := by intros; (((try have := Light.Std.space_le (by assumption)));
                                                                       ((try have := Light.Std.const_le (by assumption)));
                                                                       (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + body.blockCost + 7) + hi.cost + 5 ≤ T := by first
                                                                       |
                                                                         ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                               List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                           (first
                                                                             | omega
                                                                             | ((ring_nf); (omega))))
                                                                       | omega
                                                                       |
                                                                         (simp [] <;>
                                                                             first
                                                                             | omega
                                                                             | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q := by
  refine Ends.forMem I n body.blockCost start ?_ ?_ ?_ hn hT
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact round j μ' hj hI
  · intro μ' hI
    rw [update_frame_setLocal]
    exact done μ' hI
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact bound j μ' hj hI
theorem SolvesN.meets {task : TaskN} {P₀ : Program} {p : ℕ} {T₀ : List ℕ → ℕ}
    {need : List ℕ → Need} (h : SolvesN task P₀ p T₀ need) (R : Program) {lim : Limits} {d : ℕ}
    (x : task.Inst) {μ : ℕ → ℤ} {fr : ℕ} (hpre : task.Pre x μ fr)
    (hok : (need (task.pars x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.pars x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩

theorem Ends.callLast {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ}
    {args : List Expr} {vals : List ℤ} {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop}
    (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals)
    (hd : d < lim.depth)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) :
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT

theorem Ends.callTo {p : ℕ} {args : List Expr} {x : ℕ} {vals : List ℤ} {T' : ℕ}
    {R : ℤ → (ℕ → ℤ) → Prop}
    (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals)
    (hd : d < lim.depth) (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) :
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
    Ends.callLast (loc:=frame l) (l:=l) hp
      (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

theorem Ends.callToThen {p : ℕ} {args : List Expr} {x : ℕ} {s : Stmt}
    {vals : List ℤ} {T' : ℕ} {R : ℤ → (ℕ → ℤ) → Prop}
    (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals)
    (hd : d < lim.depth)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) :
    Ends lim P d ((Light.Stmt.seq (.call p args x) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

theorem Need.Ok.mono {r r' : Need} {lim : Limits} {fr fr' d d' : ℕ} (h : r.Ok lim fr d)
    (hw : r'.word ≤ r.word) (hc : fr' + r'.cells ≤ fr + r.cells)
    (hd : d' + r'.depth ≤ d + r.depth) : r'.Ok lim fr' d' :=
  ⟨le_trans (by exact_mod_cast hw) h.word, hc.trans h.cells, h.space, hd.trans h.depth⟩

theorem one_le_polyBound (s k : ℕ) (params : List ℕ) : 1 ≤ polyBound s k params := by
  have : 0 < (params.map (· + 1)).prod := List.prod_pos (by simp)
  exact Nat.mul_pos (by positivity) (by positivity)

theorem polyBound_mul (s s' k : ℕ) (params : List ℕ) :
    2 ^ s' * polyBound s k params = polyBound (s' + s) k params := by
  simp only [polyBound, pow_add, mul_assoc]

theorem polyBound_le_succ (s k : ℕ) (ps : List ℕ) :
    polyBound s k ps + 1 ≤ polyBound (1 + s) k ps := by
  have h1 := one_le_polyBound s k ps
  rw [← polyBound_mul]
  omega
end Light

namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
variable {lim : Limits} {d : ℕ}
namespace LopHosts
theorem rational_lop_length_thinOut (N D : ℕ) (X Y : List ℤ) {WI WJ : List ℕ} {w : ℕ}
    (h1 : WI.length = w) (h2 : WJ.length = w) :
    (thinOut N D X Y WI WJ).length = w := by
  simp [thinOut, h1, h2]

theorem rational_lop_detect_spec {P₀ R : Program} {p : ℕ} {Tn : List ℕ → ℕ}
    {need : List ℕ → Need} (hsol : SolvesN lopCountTask P₀ p Tn need)
    {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : lopDetectTask.Pre x μ fr)
    (hok : (lopDetectNeed need (lopDetectTask.pars x)).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (lopDetectBody p)
      ⟨Light.frame (lopDetectTask.args x ++ [(fr : ℤ)]), μ⟩
      (lopDetectTime Tn (lopDetectTask.pars x))
      (fun σ' => lopDetectTask.Post x μ fr (σ'.loc 0) σ'.mem) := by
  have hdep : d + ((need [x.N, x.D, x.w]).depth + 1) ≤ lim.depth := hok.depth
  have hpreCount : lopCountTask.Pre x μ fr := ⟨hpre.1, hpre.2.1, hpre.2.2⟩
  have hlen := rational_lop_length_thinOut x.N x.D x.X x.Y hpre.1.lenWI hpre.1.lenWJ
  have hfr : (fr : ℤ) ≤ lim.word := by
    have hfrSpace : fr ≤ lim.space := by have hc := hok.cells; omega
    have hcast : (fr : ℤ) ≤ (lim.space : ℤ) := by exact_mod_cast hfrSpace
    exact hcast.trans hok.space
  have hwordx : (x.w : ℤ) ≤ lim.word := by
    have hxf : x.w ≤ fr := by have := hpre.1.belowOut; omega
    have hcast : (x.w : ℤ) ≤ (fr : ℤ) := by exact_mod_cast hxf
    exact hcast.trans hfr
  have hm : Meets lim (P₀ ++ R) p (d + 1)
      [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
      (Tn [x.N, x.D, x.w]) (fun _ μ₁ =>
        Seg μ₁ x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧
        KeptBut μ μ₁ fr x.out x.w) := by
    have hokCount : (need [x.N, x.D, x.w]).Ok lim fr (d + 1) := by
      refine hok.mono le_rfl le_rfl ?_
      change d + 1 + (need [x.N, x.D, x.w]).depth ≤
        d + ((need [x.N, x.D, x.w]).depth + 1)
      omega
    exact hsol.meets R x hpreCount hokCount
  change Ends lim (P₀ ++ R) d (lopDetectBody p)
    ⟨Light.frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
    (Tn [x.N, x.D, x.w] + 20 * x.w + 18) _
  refine Ends.callToThen (p:=p) (args:=[v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9])
    (x:=10) (s:=.for 10 (v 2)
      (.ite (Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v 8) (v 10))) (k 0)) .skip
        (.store ((Light.Expr.op Light.Op.add) (v 8) (v 10)) (k 1))))
    (vals:=[x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr])
    (T':=Tn [x.N, x.D, x.w]) (R:=fun _ μ₁ =>
      Seg μ₁ x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ₁ fr x.out x.w)
    hm (fun r μ₁ hR => ?_) ?_ ?_ ?_
  rcases hR with ⟨hseg, hk⟩
  let f : ℕ → ℤ := fun i => if μ₁ (x.out + i) = 0 then 0 else 1
  have hf : ∀ i, f i = if μ₁ (x.out + i) = 0 then 0 else 1 := by intro i; rfl
  refine Ends.forFrame (fun j μ' => μ' = wrote μ₁ x.out f j) x.w wrote_zero.symm ?round ?done
    (hT := by simp; omega)
  ·
    rintro j _ hj rfl
    have hread : wrote μ₁ x.out f j (x.out + j) = μ₁ (x.out + j) := wrote_rest (by omega)
    have hfrSpace : fr ≤ lim.space := by have h := hok.cells; omega
    have hbelowOut : x.out + x.w ≤ fr := hpre.1.belowOut
    have haddrNat : x.out + j < lim.space := by omega
    have hsumWord : (x.out + j : ℤ) ≤ lim.word := by
      have hn : x.out + j ≤ fr := by omega
      have hnZ : (x.out + j : ℤ) ≤ (fr : ℤ) := by exact_mod_cast hn
      exact hnZ.trans hfr
    have hwordOne : (1 : ℤ) ≤ lim.word := by
      have hn : 1 ≤ x.w := by omega
      have hnZ : (1 : ℤ) ≤ (x.w : ℤ) := by exact_mod_cast hn
      exact hnZ.trans hwordx
    have hOpSafe :
        (Light.Expr.op Light.Op.add (v 8) (v 10)).Safe lim
          ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j), wrote μ₁ x.out f j⟩ := by
      simp only [Light.Expr.Safe, Light.Expr.val, Light.Op.eval]
      constructor
      · trivial
      · constructor
        · trivial
        · have hv :
              (Light.Op.add.eval ((v 8).val ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j),
                wrote μ₁ x.out f j⟩) ((v 10).val ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j),
                wrote μ₁ x.out f j⟩)) = (x.out + j : ℤ) := by
            simp [Light.Expr.val, Light.Op.eval, Light.frame, Light.setLocal]
          simp [Light.frame, Light.setLocal]
          rw [abs_of_nonneg (by positivity)]
          exact hsumWord
    have hLoadSafe :
        (M (Light.Expr.op Light.Op.add (v 8) (v 10))).Safe lim
          ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j), wrote μ₁ x.out f j⟩ := by
      constructor
      · exact hOpSafe
      · have hv :
            (Light.Expr.op Light.Op.add (v 8) (v 10)).val
              ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j), wrote μ₁ x.out f j⟩ =
              (x.out + j : ℤ) := by
          simp [Light.Expr.val, Light.Op.eval, Light.frame, Light.setLocal]
        rw [hv]
        exact ⟨by positivity, by exact_mod_cast haddrNat⟩
    have hCondSafe :
        (Light.Cond.eq (M (Light.Expr.op Light.Op.add (v 8) (v 10))) (k 0)).Safe lim
          ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j), wrote μ₁ x.out f j⟩ := by
      constructor
      · exact hLoadSafe
      · change (0 : ℤ) ≤ lim.word
        exact le_trans (Int.natCast_nonneg _) hok.space
    have hidx : (↑x.out + ↑j : ℤ).toNat = x.out + j := by rfl
    have hstoreSafe :
        (Light.Expr.op Light.Op.add (v 8) (v 10)).Gives lim
          ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j), wrote μ₁ x.out f j⟩ (x.out + j) ∧
        (k 1).Gives lim
          ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j), wrote μ₁ x.out f j⟩ 1 ∧
        x.out + j < lim.space := by
      constructor
      · constructor
        · exact hOpSafe
        · rfl
      · constructor
        · constructor
          · change (1 : ℤ) ≤ lim.word
            exact hwordOne
          · rfl
        · exact haddrNat
    rw [← wrote_succ]
    refine Ends.iteLast (fun hc => Ends.skip ⟨rfl, ?_⟩)
      (fun hc => Ends.storeTo (x.out + j) 1 ⟨rfl, ?_⟩ (he := hstoreSafe)
        (hT := by simp [Light.Stmt.blockCost, Light.Expr.cost]))
      (hs := hCondSafe)
    · have hc' : μ₁ (x.out + j) = 0 := by
        change wrote μ₁ x.out f j ((↑x.out + ↑j : ℤ).toNat) = 0 at hc
        rw [hidx, hread] at hc
        exact hc
      have e : f j = wrote μ₁ x.out f j (x.out + j) := by rw [hf, if_pos hc', hread, hc']
      rw [e, Function.update_eq_self]
    · have hc' : μ₁ (x.out + j) ≠ 0 := by
        change ¬wrote μ₁ x.out f j ((↑x.out + ↑j : ℤ).toNat) = 0 at hc
        rw [hidx, hread] at hc
        exact hc
      rw [hf, if_neg hc']
  ·
    rintro _ rfl
    refine ⟨fun i hi => ?_, fun a ha => ?_⟩
    ·
      have hi' : i < x.w := by simpa [hlen] using hi
      rw [List.getElem_map, ← hseg i (by omega), ← hf]
      change wrote μ₁ x.out f x.w (x.out + i) = f i
      exact wrote_done hi'
    ·
      change wrote μ₁ x.out f x.w a = μ a
      calc
        wrote μ₁ x.out f x.w a = μ₁ a := wrote_rest ha.2
        _ = μ a := hk a ha
  ·
    constructor
    · intro e he
      have he' : e = v 0 ∨ e = v 1 ∨ e = v 2 ∨ e = v 3 ∨ e = v 4 ∨
          e = v 5 ∨ e = v 6 ∨ e = v 7 ∨ e = v 8 ∨ e = v 9 := by
        simpa using he
      rcases he' with h | h | h | h | h | h | h | h | h | h <;> subst e <;>
        simp [Light.Expr.Safe]
    · simp [Light.frame, Light.Expr.val]
  · omega
  · simp [Light.Expr.cost, Light.Stmt.blockCost, Light.Cond.cost] <;> omega

theorem rational_polyNeedN_detect {need : List ℕ → Need} (h : PolyNeedN need) :
    PolyNeedN (lopDetectNeed need) := by
  obtain ⟨s, e, h⟩ := h
  refine ⟨1 + s, e, fun ps => ?_⟩
  have h1 := Light.polyBound_le_succ s e ps
  obtain ⟨a, b, c⟩ := h ps
  simp only [lopDetectNeed]
  omega


end LopHosts

theorem rational_claim_lopDetectFromCount : Claim.LopDetectFromCount lightModel := by
  refine ⟨20, fun T hT => ?_⟩
  obtain ⟨P, p, Tn, need, hneed, hsol, htime⟩ := hT
  refine ⟨P ++ [lopDetectBody p], P.length, lopDetectTime Tn, lopDetectNeed need,
    LopHosts.rational_polyNeedN_detect hneed, ?_, fun n D w w' hn hD hw => ?_⟩
  · refine ⟨lopDetectBody p, by simp, fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact LopHosts.rational_lop_detect_spec hsol hpre hok
  · have h1 := htime n D w w' hn hD hw
    have h2 : (w : ℝ) ≤ w' := by exact_mod_cast hw
    simp only [lopDetectTime, List.getD_cons_succ, List.getD_cons_zero]
    push_cast
    linarith


end Light.Sec3

#print axioms Light.Sec3.LopHosts.rational_lop_detect_spec
#print axioms Light.Sec3.rational_claim_lopDetectFromCount
