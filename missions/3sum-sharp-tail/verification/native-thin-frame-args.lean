import Mathlib
import Definitions.Def_APSP299791_Defs5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Light.Sec2

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

def thinFrameArgs (x : ThinInst) : List Expr :=
  [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9]

def thinFrameArgs01 : List Expr := [v 0, v 1]

def thinFrameLocs (x : ThinInst) (fr : ℕ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), (x.U : ℤ), (x.x : ℤ), (x.y : ℤ),
    (x.wi : ℤ), (x.wj : ℤ), (x.out : ℤ), (fr : ℤ)]

def thinFrameState (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (r : ℤ) : State :=
  ⟨frame (setLocal (thinFrameLocs x fr) 10 r), μ⟩

theorem thinFrame_args_safe (lim : Limits) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (r : ℤ)
    (_std : Std lim) (_hpre : x.Pre μ fr) (_hfr : fr ≤ lim.space)
    (_hU : x.U = 1) (_hr : |r| ≤ lim.word) :
    ∀ e ∈ thinFrameArgs x, e.Safe lim (thinFrameState x μ fr r) := by
  intro e _he
  simp only [thinFrameArgs, List.mem_cons, List.mem_singleton] at _he
  rcases _he with h | h | h | h | h | h | h | h | h | h <;>
    simp_all [Expr.Safe, v]

theorem thinFrame_args_vals (lim : Limits) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (r : ℤ)
    (_std : Std lim) (_hpre : x.Pre μ fr) (_hfr : fr ≤ lim.space)
    (_hU : x.U = 1) (_hr : |r| ≤ lim.word) :
    (thinFrameArgs x).map (fun e => e.val (thinFrameState x μ fr r)) =
      [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), (x.U : ℤ), (x.x : ℤ), (x.y : ℤ),
        (x.wi : ℤ), (x.wj : ℤ), (x.out : ℤ), (fr : ℤ)] := by
  simp [thinFrameArgs, thinFrameState, thinFrameLocs, Expr.val, frame_setLocal,
    Light.frame]

theorem thinFrame_args01_safe (lim : Limits) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (r : ℤ)
    (_std : Std lim) (_hpre : x.Pre μ fr) (_hfr : fr ≤ lim.space)
    (_hU : x.U = 1) (_hr : |r| ≤ lim.word) :
    ∀ e ∈ thinFrameArgs01, e.Safe lim (thinFrameState x μ fr r) := by
  intro e _he
  simp only [thinFrameArgs01, List.mem_cons, List.mem_singleton] at _he
  rcases _he with h | h <;> simp_all [Expr.Safe, v]

theorem thinFrame_args01_vals (lim : Limits) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (r : ℤ)
    (_std : Std lim) (_hpre : x.Pre μ fr) (_hfr : fr ≤ lim.space)
    (_hU : x.U = 1) (_hr : |r| ≤ lim.word) :
    (thinFrameArgs01).map (fun e => e.val (thinFrameState x μ fr r)) =
      [(x.N : ℤ), (x.D : ℤ)] := by
  simp [thinFrameArgs01, thinFrameState, thinFrameLocs, Expr.val, frame_setLocal,
    Light.frame]

end Light.Sec2
