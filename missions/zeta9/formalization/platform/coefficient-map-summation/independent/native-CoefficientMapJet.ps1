$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-summation/independent/cache/n;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-summation/independent/cache/n/missions/zeta9/formalization/CoefficientMapJet.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/CoefficientMapJet.lean"
exit $LASTEXITCODE
