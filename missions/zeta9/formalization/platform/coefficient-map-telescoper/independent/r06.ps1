$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ti1/b/n/lib/lean;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p"
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ti1/b/n/lib/lean/NativeValueComparisonDefinition.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p/NativeValueComparisonDefinition.lean"
exit $LASTEXITCODE
