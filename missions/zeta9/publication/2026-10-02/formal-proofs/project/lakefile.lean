import Lake
open Lake DSL

package zeta9FormalProofs where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib Definitions where
  roots := #[]
  globs := #[.submodules `Definitions]

@[default_target]
lean_lib Solutions where
  roots := #[]
  globs := #[.submodules `Solutions]
