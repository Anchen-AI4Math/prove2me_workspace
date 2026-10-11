import missions.zeta9.formalization.AnalyticPhaseUpperBound
import Lean
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
open Set
open ZetaNine.AnalyticPhase
open Lean Meta Elab Command

run_cmd liftTermElabM do
  let env ← getEnv
  for n in env.header.moduleNames do
    let found ← Lean.findOLean n
    let canonical ← IO.FS.realPath found
    let j := Json.mkObj [("kind",toJson "actual_module_resolver"),
      ("module",toJson n.toString),("found_olean",toJson found.toString),
      ("canonical_olean",toJson canonical.toString)]
    liftM <| IO.println ("PHI_RECORD|" ++ j.compress)
