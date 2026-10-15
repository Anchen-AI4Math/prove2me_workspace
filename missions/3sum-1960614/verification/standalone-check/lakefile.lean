import Lake
open Lake DSL

package ThreeSum1960614Standalone

require mathlib from "D:/users/self_projects/prove2me_workspace/.lake/packages/mathlib"

@[default_target]
lean_lib Submission where
  srcDir := "D:/users/self_projects/prove2me_workspace/missions/3sum-1960614/submission-bigospeedrun"
  roots := #[`Submission]
  globs := #[.one `Submission,.submodules `Submission]
