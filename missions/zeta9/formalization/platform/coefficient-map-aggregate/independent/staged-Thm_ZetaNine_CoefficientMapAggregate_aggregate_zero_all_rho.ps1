$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/cache/p;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/project"
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/project"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/cache/p/Theorems/Thm_ZetaNine_CoefficientMapAggregate_aggregate_zero_all_rho.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/project/Theorems/Thm_ZetaNine_CoefficientMapAggregate_aggregate_zero_all_rho.lean"
exit $LASTEXITCODE
