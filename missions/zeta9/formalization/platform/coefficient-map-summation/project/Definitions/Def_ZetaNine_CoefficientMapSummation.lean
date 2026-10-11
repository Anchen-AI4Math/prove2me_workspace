import Definitions.Def_ZetaNine_CoefficientMapReflection
import Definitions.Def_ZetaNine_CoefficientMapFiniteSum
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapSummation

open scoped BigOperators Topology
open Finset Polynomial Filter
open HarmonicStability CoefficientMapInjectivity CoefficientMapReflection

def zetaReal (s : ℕ) : ℝ := (riemannZeta (s : ℂ)).re

def exactL (n : ℕ) (W : ℚ[X]) : ℝ :=
  (CoefficientMapFiniteSum.constantTerm n W : ℝ) +
    ((CoefficientMapFiniteSum.rho n 3 W : ℝ) * zetaReal 3 +
     (CoefficientMapFiniteSum.rho n 5 W : ℝ) * zetaReal 5 +
     (CoefficientMapFiniteSum.rho n 7 W : ℝ) * zetaReal 7 +
     (CoefficientMapFiniteSum.rho n 9 W : ℝ) * zetaReal 9)

def actualSeries (n : ℕ) (W : ℚ[X]) (t : ℕ) : ℝ :=
  (CoefficientMap.weightedR n W ((t + 1 : ℕ) : ℚ) : ℝ)

end ZetaNine.CoefficientMapSummation
