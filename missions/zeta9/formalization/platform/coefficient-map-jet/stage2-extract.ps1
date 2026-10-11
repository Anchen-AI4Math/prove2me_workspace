$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-jet/build/original;D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map/build/original;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean --run "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-jet/extract_sketch_info.lean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/CoefficientMapJet.lean" "ZetaNine"
exit $LASTEXITCODE
