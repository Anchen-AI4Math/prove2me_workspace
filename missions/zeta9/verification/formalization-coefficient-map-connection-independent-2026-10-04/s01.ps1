$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ci1/b;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace/missions/zeta9/verification/formalization-coefficient-map-connection-independent-2026-10-04/p"
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/verification/formalization-coefficient-map-connection-independent-2026-10-04/p"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ci1/b/missions/zeta9/formalization/CoefficientMapConnection.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/verification/formalization-coefficient-map-connection-independent-2026-10-04/p/missions/zeta9/formalization/CoefficientMapConnection.lean"
exit $LASTEXITCODE
