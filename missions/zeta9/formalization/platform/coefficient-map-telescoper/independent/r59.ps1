$env:LEAN_NUM_THREADS = "1"
$blockedRootProofCache = "d:/users/self_projects/prove2me_workspace/.lake/build/lib/lean"
$packagePathEntries = @($env:LEAN_PATH -split ";" | Where-Object { $_ -and ([System.IO.Path]::GetFullPath($_).Replace("\", "/").TrimEnd("/").ToLowerInvariant() -ne $blockedRootProofCache) })
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ti1/b/n/lib/lean;" + ($packagePathEntries -join ";") + ";D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p"
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/p"
& lean "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-telescoper/independent/agg-native-values.lean"
exit $LASTEXITCODE
