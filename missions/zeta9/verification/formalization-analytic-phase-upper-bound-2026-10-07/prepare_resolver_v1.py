"""Prepare actual Lean-loader canonical path inventory; no proof objects imported from peers."""
import sys
sys.dont_write_bytecode=True
import prepare_native as p
from prepare_controls_v1 import IMPORT

def main():
    source=IMPORT+'''
run_cmd liftTermElabM do
  let env ← getEnv
  for n in env.header.moduleNames do
    let found ← Lean.findOLean n
    let canonical ← IO.FS.realPath found
    let j := Json.mkObj [("kind",toJson "actual_module_resolver"),
      ("module",toJson n.toString),("found_olean",toJson found.toString),
      ("canonical_olean",toJson canonical.toString)]
    liftM <| IO.println ("AP_RECORD|" ++ j.compress)
'''
    p.write(p.PROJECT/'APResolver.lean',source);p.write(p.OUT/'controls-resolver-v1/APResolver.lean',source)
    p.dump(p.OUT/'resolver-control-preparation-v1.json',dict(control=p.binding(p.PROJECT/'APResolver.lean'),
      actual_findOLean_and_IO_FS_realPath=True,pinned_intrinsic_Lean_toolchain_allowed=True,
      only_own_aph1_and_fixed_Mathlib_packages_community_objects=True,foreign_mission_proof_objects=False))
    print('Actual loader/canonical resolver source prepared.',flush=True)
if __name__=='__main__':main()
