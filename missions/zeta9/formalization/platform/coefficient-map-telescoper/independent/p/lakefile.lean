import Lake
open Lake DSL
package zeta9TelescoperIndependent where
  buildDir := "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ti1/b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
