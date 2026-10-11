$env:LEAN_NUM_THREADS = "1"
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-finite-sum/independent/cache/p;" + $env:LEAN_PATH + ";D:/users/self_projects/prove2me_workspace"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-finite-sum/independent/cache/p/Theorems/Thm_ZetaNine_CoefficientMapFiniteSum_harmonic_difference_eq_shifted.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-finite-sum/staged/Theorems/Thm_ZetaNine_CoefficientMapFiniteSum_harmonic_difference_eq_shifted.lean"
exit $LASTEXITCODE
