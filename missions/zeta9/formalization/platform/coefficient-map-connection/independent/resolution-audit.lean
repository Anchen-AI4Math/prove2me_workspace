import Lean
open Lean
run_meta do
  for n in [`missions.zeta9.formalization.CoefficientMapConnection, `Definitions.Def_ZetaNine_CoefficientMapConnection, `Solutions.Sol_ZetaNine_CoefficientMapConnection_connection_homogeneous_kernel_zero, `Theorems.Thm_ZetaNine_CoefficientMapConnection_connection_homogeneous_kernel_zero, `Solutions.Sol_ZetaNine_CoefficientMapConnection_connectionLinearMap_bijective, `Theorems.Thm_ZetaNine_CoefficientMapConnection_connectionLinearMap_bijective, `Solutions.Sol_ZetaNine_CoefficientMapConnection_connection_five_systems_unique, `Theorems.Thm_ZetaNine_CoefficientMapConnection_connection_five_systems_unique] do
    let p ← findOLean n
    IO.println (Json.mkObj [("module",toJson n.toString),("olean",toJson p.toString)]).compress
