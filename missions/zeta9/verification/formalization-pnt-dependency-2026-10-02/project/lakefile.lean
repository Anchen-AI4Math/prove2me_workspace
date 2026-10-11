import Lake
open Lake DSL

package zeta9PntKernelReplay

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib Architect where
  roots := #[`Architect]
  globs := #[.one `Architect, .submodules `Architect]

lean_lib PrimeNumberTheoremAnd where
  roots := #[`PrimeNumberTheoremAnd.MediumPNT]
  globs := #[.submodules `PrimeNumberTheoremAnd]
