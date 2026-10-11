$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map/build/staged;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map/build/staged/Definitions/Def_ZetaNine_CoefficientMap.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map/staged/Definitions/Def_ZetaNine_CoefficientMap.lean"
exit $LASTEXITCODE
