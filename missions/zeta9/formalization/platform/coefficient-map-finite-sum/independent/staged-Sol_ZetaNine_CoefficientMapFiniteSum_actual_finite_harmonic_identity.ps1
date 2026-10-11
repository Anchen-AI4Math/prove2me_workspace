$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-finite-sum/independent/cache/p;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-finite-sum/independent/cache/p/Solutions/Sol_ZetaNine_CoefficientMapFiniteSum_actual_finite_harmonic_identity.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-finite-sum/staged/Solutions/Sol_ZetaNine_CoefficientMapFiniteSum_actual_finite_harmonic_identity.lean"
exit $LASTEXITCODE
