$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/cache/n;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/project"
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/project"
& lean --run "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/extract-boundary-author.lean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-aggregate/independent/project/boundary-author-input.lean"
exit $LASTEXITCODE
