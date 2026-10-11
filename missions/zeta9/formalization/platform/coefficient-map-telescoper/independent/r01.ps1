$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ti1/b/p/lib/lean;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p"
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ti1/b/p/lib/lean/Definitions/Def_ZetaNine_HarmonicStability.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p/Definitions/Def_ZetaNine_HarmonicStability.lean"
exit $LASTEXITCODE
