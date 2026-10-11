import Lake
open Lake DSL
package «zeta9_research» where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib «Zeta9Research» where
  roots := #[`Theorems.Thm_Zeta9Note_min_lt_weighted_average_lt_max,
             `Theorems.Thm_Zeta9Note_quadrature_exact_of_moments,
             `Theorems.Thm_ZetaNine_exponentially_small_independent_forms_of_zeta_nine,
             `Theorems.Thm_ZetaNine_exponentially_small_nonzero_forms_of_zeta_nine,
             `Theorems.Thm_ZetaNine_irrational_of_small_nonzero_integer_forms,
             `Theorems.Thm_ZetaNine_irrational_of_two_small_integer_forms,
             `Theorems.Thm_ZetaNine_min_lt_weighted_average_lt_max,
             `Theorems.Thm_ZetaNine_quadrature_exact_of_moments]
