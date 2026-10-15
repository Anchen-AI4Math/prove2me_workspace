import Submission.ThreeSum.LightLocalCoverInit

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Light ThreeSum.LightLocalCoverInit ThreeSum.LightLocalCoverLayout
open ThreeSum.LightLocalCoverTables ThreeSum.LightLocalCoverSchedule ThreeSum.GlobalEncoding

theorem solution {lim : Limits} {μ : ℕ→ℤ} {free h d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+464*h+9 ≤ lim.depth)
    (hspace : ThreeSum.LightLocalCoverInit.space free h ≤ lim.space)
    (hword : (ThreeSum.LightLocalCoverInit.word h : ℤ) ≤ lim.word) :
    Meets lim ThreeSum.LightLocalCoverInit.program 52 d [h,free] μ (ThreeSum.LightLocalCoverInit.time h)
      (fun r ν => r=(ThreeSum.LightLocalCoverMetadata.nextFree (base free) h : ℤ) ∧
        Seg ν free (ThreeSum.LightLocalCoverInit.values free h) ∧
        Data ν h (maps (base free) h) (hist0 (base free) h)
          (hist1 (base free) h) (matrixPtr (base free) h) ∧
        ScheduleRows ν h (scheduleMaps (base free) h) ∧
        (∀ s : Occurrence h, ν (candidates (base free) h+s.val)=(candidateAt h s : ℤ)) ∧
        Kept μ ν free) := by
  exact programProcs.meets hw hd hspace hword

#print axioms solution
