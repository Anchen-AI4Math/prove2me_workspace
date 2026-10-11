$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/cache/n;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/project"
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/project"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/cache/n/Definitions/Def_ZetaNine_HarmonicStability.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/project/Definitions/Def_ZetaNine_HarmonicStability.lean"
exit $LASTEXITCODE
