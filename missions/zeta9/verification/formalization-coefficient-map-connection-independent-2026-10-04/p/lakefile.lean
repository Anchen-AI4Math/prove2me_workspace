import Lake
open Lake DSL
package connectionIndependent where
  buildDir := "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ci1/b"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapConnection]
