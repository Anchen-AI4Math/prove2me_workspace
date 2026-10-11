import Theorems.Thm_ZetaNine_AnalyticUniformMomentBound_actualMoment_uniform_bound
import Theorems.Thm_ZetaNine_AnalyticWeightedBound_changing_quartics_uniform_bound
import Theorems.Thm_ZetaNine_AnalyticWeightedBound_actual_weighted_uniform_o_one
import Lean
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
open ZetaNine
open Lean Meta Elab Command
open ZetaNine.AnalyticMomentBounds
open ZetaNine.AnalyticPhase
open ZetaNine.AnalyticUniformMomentBound
open ZetaNine.AnalyticWeightedBound
open ZetaNine.CoefficientMap

run_cmd liftTermElabM do
  let env ← getEnv
  for n in env.header.moduleNames do
    let found ← Lean.findOLean n
    let canonical ← IO.FS.realPath found
    liftM <| IO.println ("GAI_RECORD|" ++ (Json.mkObj [("kind",toJson "actual_module_resolver"),
      ("module",toJson n.toString),("found_olean",toJson found.toString),
      ("canonical_olean",toJson canonical.toString)]).compress)
