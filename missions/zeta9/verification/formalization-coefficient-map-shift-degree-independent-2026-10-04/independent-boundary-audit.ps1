$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/verification/formalization-coefficient-map-shift-degree-independent-2026-10-04/native/build;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean "D:/users/self_projects/prove2me_workspace/missions/zeta9/verification/formalization-coefficient-map-shift-degree-independent-2026-10-04/independent-boundary-audit.lean"
exit $LASTEXITCODE
