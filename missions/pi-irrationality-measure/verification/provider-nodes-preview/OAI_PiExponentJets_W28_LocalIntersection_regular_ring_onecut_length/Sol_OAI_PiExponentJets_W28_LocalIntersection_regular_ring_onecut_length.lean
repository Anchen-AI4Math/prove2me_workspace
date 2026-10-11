import Definitions.Def_OAI_NumberTheory_PiExponent_Cohomology_LocalIntersectionRegularEuler
import Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalIntersectionLength
import Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalIntersectionPrimeFactors
import Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_ParameterKilledFiniteLength
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic
import Theorems.Thm_OAI_PiExponentJets_W28_LocalIntersection_exists_regular_onecut_sum_and_local_counts

section


namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [IsLocalRing A]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A] in
private theorem _p2m_inline_4c9c5f1da63f140710c4
    (S : Set (Ideal A)) [Fintype S] (P : Ideal A) (w : Ideal A → ℕ∞) :
    (∑ Q : S, if P = Q.val then w Q.val else 0) =
      if P ∈ S then w P else 0 := by
  classical
  by_cases hp : P ∈ S
  · rw [if_pos hp]
    calc
      (∑ Q : S, if P = Q.val then w Q.val else 0) =
          (if P = P then w P else 0) := by
        apply Finset.sum_eq_single (⟨P, hp⟩ : S)
        · intro Q hQ hne
          have hne' : P ≠ Q.val := by
            intro h
            apply hne
            exact Subtype.ext h.symm
          simp only [hne', ↓reduceIte]
        · simp
      _ = w P := if_pos rfl
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro Q hQ
    have hne : P ≠ Q.val := fun h => hp (h.symm ▸ Q.property)
    simp only [hne, ↓reduceIte]



end PiExponentJets.W28.LocalIntersection

end OAI

end
section
open OAI OAI.PiExponentJets OAI.PiExponentJets.W28 OAI.PiExponentJets.W28.LocalIntersection
open scoped BigOperators Classical
variable {A : Type*} [CommRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [IsLocalRing A]


open Lean Meta in
run_meta do
  let requests : Array (String × Lean.Name × String) := #[("_private.OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionMinimalSum.0.OAI.PiExponentJets.W28.LocalIntersection.subtype_indicator_sum", `OAI.PiExponentJets.W28.LocalIntersection._p2m_inline_4c9c5f1da63f140710c4, "theorem")]
  let env ← Lean.getEnv
  let mut rows : Array Lean.Json := #[]
  let mut actualNames : Array Lean.Name := #[]
  for (sourceName, userName, expectedKind) in requests do
    let mut candidates : Array Lean.Name := #[]
    for (actualName, _) in env.constants.toList do
      if Lean.privateToUserName? actualName == some userName then
        if (env.getModuleIdxFor? actualName).isNone then
          candidates := candidates.push actualName
    unless candidates.size == 1 do
      throwError "Expected one OwnModule private binding for {userName}, found {candidates.size}"
    let actualName := candidates[0]!
    let some ci := env.find? actualName | throwError "Missing recovered private declaration"
    let (kind, value, safety) ← match ci with
      | .thmInfo t => pure ("theorem", t.value, Lean.Json.null)
      | .defnInfo d => pure ("def", d.value, Lean.toJson (reprStr d.safety))
      | _ => throwError "Recovered private CI is neither theorem nor definition"
    unless kind == expectedKind do
      throwError "Recovered private CI kind differs from source Graph: {actualName}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars ||
        value.hasMVar || value.hasFVar || value.hasLooseBVars then
      throwError "Recovered private CI type/value is not closed"
    let axioms ← Lean.collectAxioms actualName
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Private helper has nonstandard axioms: {actualName}"
    actualNames := actualNames.push actualName
    rows := rows.push <| Lean.Json.mkObj [
      ("sourceGraphName", Lean.toJson sourceName),
      ("nodeGeneratedName", Lean.toJson userName.toString),
      ("actualKernelName", Lean.toJson actualName.toString),
      ("kind", Lean.toJson kind), ("safety", safety),
      ("ownerKind", Lean.toJson "OwnModule"),
      ("ownModule", Lean.toJson env.mainModule.toString),
      ("moduleIndexIsNone", Lean.toJson true),
      ("levelParams", Lean.toJson (ci.levelParams.map Lean.Name.toString)),
      ("typeRefs", Lean.toJson (ci.type.getUsedConstants.map Lean.Name.toString)),
      ("valueRefs", Lean.toJson (value.getUsedConstants.map Lean.Name.toString)),
      ("snapshotValueRequired", Lean.toJson (kind == "def")),
      ("axioms", Lean.toJson (axioms.map Lean.Name.toString))]
  IO.println ("PI_ISOLATED_PRIVATE_MAP " ++ (Lean.Json.mkObj [
    ("artifact", Lean.toJson "Sol"),
    ("ownModule", Lean.toJson env.mainModule.toString),
    ("rows", Lean.Json.arr rows)]).compress)
theorem solution (x : A) (hx : x ∈ nonZeroDivisors A) :
    Module.length A (A ⧸ Ideal.span {x}) =
      OAI.PiExponentJets.W28.LocalIntersection.minimalPrimeCutSum (⊥ : Ideal A) x := open OAI OAI.PiExponentJets OAI.PiExponentJets.W28 OAI.PiExponentJets.W28.LocalIntersection in by
  classical
  obtain ⟨n, J, f, hp, he, hcounts⟩ := OAI.PiExponentJets.W28.LocalIntersection.exists_regular_onecut_sum_and_local_counts x hx
  let ps : ℕ → Ideal A := fun i => (J i).colon {f i}
  let w : Ideal A → ℕ∞ := fun P => Module.length A (A ⧸ (P ⊔ Ideal.span {x}))
  have hsumNat : (Module.length A (A ⧸ Ideal.span {x})).toNat =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then (w (ps i)).toNat else 0 := by
    exact_mod_cast he
  have hsumENat : ((Module.length A (A ⧸ Ideal.span {x})).toNat : ℕ∞) =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then ((w (ps i)).toNat : ℕ∞) else 0 := by
    exact_mod_cast hsumNat
  have hzeroCut : Module.length A (A ⧸ Ideal.span {x}) ≠ ⊤ := by
    exact Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton A hx)
  rw [ENat.natCast_toNat hzeroCut] at hsumENat
  have hsum : Module.length A (A ⧸ Ideal.span {x}) =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then w (ps i) else 0 := by
    refine hsumENat.trans (Finset.sum_congr rfl ?_)
    intro i hi
    split_ifs with hmin
    · exact ENat.natCast_toNat (OAI.PiExponentJets.W28.LocalIntersection.regular_cut_length_ne_top x hx (ps i))
    · rfl
  let : Fintype ((⊥ : Ideal A).minimalPrimes) :=
    ((⊥ : Ideal A).finite_minimalPrimes_of_isNoetherianRing A).fintype
  have hterm (P : (⊥ : Ideal A).minimalPrimes) :
      (letI : P.val.IsPrime := P.property.1.1
       Module.length (Localization.AtPrime P.val)
          (Localization.AtPrime P.val ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P.val))) * w P.val) =
        ∑ i ∈ Finset.range n, if ps i = P.val then w P.val else 0 := by
    let : P.val.IsPrime := P.property.1.1
    rw [hcounts P.val P.property, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : ps i = P.val
    · simp only [ps] at h
      simp only [h, ↓reduceIte, one_mul, ps]
    · simp only [ps] at h
      simp only [h, ↓reduceIte, zero_mul, ps]
  calc
    Module.length A (A ⧸ Ideal.span {x}) =
        ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then w (ps i) else 0 := hsum
    _ = ∑ i ∈ Finset.range n, ∑ P : (⊥ : Ideal A).minimalPrimes,
        if ps i = P.val then w P.val else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (OAI.PiExponentJets.W28.LocalIntersection._p2m_inline_4c9c5f1da63f140710c4 ((⊥ : Ideal A).minimalPrimes) (ps i) w).symm
    _ = ∑ P : (⊥ : Ideal A).minimalPrimes, ∑ i ∈ Finset.range n,
        if ps i = P.val then w P.val else 0 := Finset.sum_comm
    _ = OAI.PiExponentJets.W28.LocalIntersection.minimalPrimeCutSum (⊥ : Ideal A) x := by
      unfold OAI.PiExponentJets.W28.LocalIntersection.minimalPrimeCutSum
      apply Finset.sum_congr rfl
      intro P hP
      exact (hterm P).symm

end

#print axioms solution
