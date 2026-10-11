$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-jet/build/staged;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-jet/types_2_reference.lean"
exit $LASTEXITCODE
