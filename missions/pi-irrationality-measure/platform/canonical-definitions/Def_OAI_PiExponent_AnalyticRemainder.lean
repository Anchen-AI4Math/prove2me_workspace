import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily

noncomputable section
namespace OAI.PiExponent.DeterminantContradiction

-- Real polynomial majorant of TranslationCountLimit.translationTermCount.
def translationEnvelope (m : ℕ) (v H : ℝ) : ℝ :=
  (H + 1) ^ (2 * m) * (H / v + 1)

-- CollisionExponential.collisionRemainder, plus the translation entropy.
def analyticRemainder {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  (Real.log (actualRowCount d H : ℝ) + Real.log 2 / 4 -
    Real.log (1 - Real.exp (-Real.log 2 / 2))) / H +
    Real.log (translationEnvelope d.m d.v0 H) / H

end OAI.PiExponent.DeterminantContradiction
