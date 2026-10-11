$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-summation/independent/cache/p;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-summation/independent/cache/p/Definitions/Def_ZetaNine_HarmonicStability.olean" "D:/users/self_projects/prove2me_workspace/Definitions/Def_ZetaNine_HarmonicStability.lean"
exit $LASTEXITCODE
