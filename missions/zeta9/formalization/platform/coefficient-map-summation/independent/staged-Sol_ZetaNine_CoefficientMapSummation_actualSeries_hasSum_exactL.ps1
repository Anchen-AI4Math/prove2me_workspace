$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-summation/independent/cache/p;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-summation/independent/cache/p/Solutions/Sol_ZetaNine_CoefficientMapSummation_actualSeries_hasSum_exactL.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-summation/staged/Solutions/Sol_ZetaNine_CoefficientMapSummation_actualSeries_hasSum_exactL.lean"
exit $LASTEXITCODE
