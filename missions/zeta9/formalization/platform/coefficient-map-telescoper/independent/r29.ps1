$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ti1/b/p/lib/lean;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p"
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ti1/b/p/lib/lean/Solutions/Sol_ZetaNine_CoefficientMapTelescoper_actual_polynomial_quotient_degree_bound.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p/Solutions/Sol_ZetaNine_CoefficientMapTelescoper_actual_polynomial_quotient_degree_bound.lean"
exit $LASTEXITCODE
