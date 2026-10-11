$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map/build/original;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map/build/original/missions/zeta9/formalization/CoefficientMap.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/CoefficientMap.lean" 
exit $LASTEXITCODE
