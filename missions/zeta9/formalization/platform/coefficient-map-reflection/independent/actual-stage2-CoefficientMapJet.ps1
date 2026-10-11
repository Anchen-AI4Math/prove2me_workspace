$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-reflection/independent/cache/native/build;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean --run "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-reflection/independent/extract-native-CoefficientMapJet.lean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/CoefficientMapJet.lean" "ZetaNine"
exit $LASTEXITCODE
