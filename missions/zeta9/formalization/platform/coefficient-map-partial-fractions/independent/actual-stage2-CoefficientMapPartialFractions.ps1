$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-partial-fractions/independent/cache/native/build;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean --run "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-partial-fractions/independent/extract-native-CoefficientMapPartialFractions.lean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/CoefficientMapPartialFractions.lean" "ZetaNine"
exit $LASTEXITCODE
