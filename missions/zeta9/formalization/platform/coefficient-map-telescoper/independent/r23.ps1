$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ti1/b/n/lib/lean;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p"
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p"
& lean --run "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/cp1.lean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p/NativeTelescoperIndependentControl.lean"
exit $LASTEXITCODE
