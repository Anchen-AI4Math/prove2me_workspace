import Lake
open Lake DSL

package zeta9AdvancedProofs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib Architect where
  roots := #[`Architect]
  globs := #[.one `Architect, .submodules `Architect]

lean_lib PrimeNumberTheoremAnd where
  roots := #[`PrimeNumberTheoremAnd.MediumPNT]
  globs := #[.submodules `PrimeNumberTheoremAnd]

lean_lib Definitions where
  roots := #[]
  globs := #[.submodules `Definitions]

lean_lib Theorems where
  roots := #[]
  globs := #[.submodules `Theorems]

lean_lib Solutions where
  roots := #[]
  globs := #[.submodules `Solutions]

lean_lib Native where
  roots := #[]
  globs := #[.submodules `missions.zeta9.formalization]

@[default_target]
lean_lib Audit where
  roots := #[]
  globs := #[.submodules `Audit]
