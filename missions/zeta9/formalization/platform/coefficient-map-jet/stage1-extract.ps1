$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-jet/build/original;D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map/build/original;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-jet/extract_decl_graph.lean"
exit $LASTEXITCODE
