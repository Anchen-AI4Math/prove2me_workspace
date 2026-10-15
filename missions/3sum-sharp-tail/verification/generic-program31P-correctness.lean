/-!
Minimal extraction of the generic program-correctness section from the accepted
`Light.Sec4.allInstancesP_programP` source. The accepted source specializes the
outer wrapper later, but these three lemmas are polymorphic in `G : RatParams`.
This file is a reference helper for the open bridge; it is not a replacement for
the accepted source or the open 3SUM theorem.
-/

import Definitions.Def_APSP299791_Defs5
import Theorems.Thm_Light_Sec4_preCoreSpec_all
import Theorems.Thm_Light_Sec4_queryAtSpec_all
import Theorems.Thm_Light_Sec4_shared_base58

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

section

namespace Light

variable {lim : Limits} {P : Program}

theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt}
    (h : P[p]? = some body) (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

end Light

end

section

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

theorem length_base58 : base58P.length = 58 := rfl

theorem at_base58 {p : ℕ} {body : Stmt} (h : base58P[p]? = some body) (R : Program) :
    (base58P ++ R)[p]? = some body :=
  Light.getElem?_append_of_eq_some h R

theorem has40_base58 (R : Program) : Has40 (base58P ++ R) := by
  have h := has40_of_append (A := Sec2.programThin ++ prunedProcs ++ List.replicate 8 .skip)
    (B := [preCoreBodyP, queryAtBody, wantedCoreBody, wantedMainBody] ++ R) rfl
  rwa [← List.append_assoc] at h

theorem preCore_base58 (R : Program) : ∀ lim,
    PreCoreSpecP lim (base58P ++ R) cShared30 :=
  preCoreSpec_all (has40_base58 R) (at_base58 rfl R) (shared_base58 R)

theorem queryAt_base58 (R : Program) : ∀ lim,
    QueryAtSpecP lim (base58P ++ R) :=
  queryAtSpec_all (has40_base58 R) (at_base58 rfl R)

theorem program31_at (G : RatParams) (n : ℕ) {body : Stmt}
    (hn : 58 ≤ n := by norm_num)
    (h : (procs31 G)[n - 58]? = some body := by rfl) :
    (program31P G)[n]? = some body := by
  rw [program31P, List.getElem?_append_right (by rw [length_base58]; exact hn), length_base58]
  exact h

/-- The actual preprocessing specification, generic in the rational parameters `G`. -/
theorem pre31_program31 (G : RatParams) : ∀ lim,
    PreSpec31P lim (program31P G) cShared30 G := by
  intro lim N D₀ aX aY fr X Y U μ hin
  have std := hin.lim.std
  have hcopy : CopySpec lim (program31P G) := copy_ok (program31_at G Proc.copy) std
  have hfill : FillSpec lim (program31P G) := fill_ok (program31_at G Proc.fill) std
  have hlog : Log4Spec lim (program31P G) := log4_meets (program31_at G Proc.log4) std
  have hlev : CeilMulSpec lim (program31P G) Proc.levels31 G.a G.b :=
    ceilMul_meets G.hb (program31_at G Proc.levels31)
  have hswi : CeilMulSpec lim (program31P G) Proc.switch31 G.p G.q :=
    ceilMul_meets G.hq (program31_at G Proc.switch31)
  have hpad : PadXSpec lim (program31P G) :=
    padX_meets (program31_at G Proc.padX) hcopy hfill std
  exact pre31_meets G (program31_at G Proc.pre31)
    ⟨hlog, hlev, hswi, hpad, hcopy, hfill, preCore_base58 _ lim⟩ N D₀ aX aY fr X Y U μ hin

/-- The actual query specification, generic in the rational parameters `G`. -/
theorem query31_program31 (G : RatParams) : ∀ lim,
    QuerySpec31P lim (program31P G) G := by
  intro lim N D₀ aX aY fr X Y U μ I J hin
  have hip : IpAtSpec lim (program31P G) :=
    ipAt_meets (program31_at G Proc.ipAt) hin.lim.std
  exact query31_meets G (program31_at G Proc.query31) (queryAt_base58 _ lim) hip
    N D₀ aX aY fr X Y U μ I J hin

/-- The actual offline routine specification, generic in `G`. -/
theorem offline32_program31 (G : RatParams) : ∀ lim,
    OfflineSpec32P lim (program31P G) cShared30 G :=
  fun lim => offline32_meets (program31_at G Proc.offline32)
    (pre31_program31 G lim) (query31_program31 G lim)

end Light.Sec4
end
end
