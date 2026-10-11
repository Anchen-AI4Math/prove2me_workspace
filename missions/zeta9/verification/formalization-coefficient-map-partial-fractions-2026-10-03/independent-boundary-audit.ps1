$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/verification/formalization-coefficient-map-partial-fractions-2026-10-03/independent/build;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean "D:/users/self_projects/prove2me_workspace/missions/zeta9/verification/formalization-coefficient-map-partial-fractions-2026-10-03/independent-boundary-audit.lean"
exit $LASTEXITCODE
