$env:LEAN_NUM_THREADS = "1"
$allowedPackageRoot = "d:/users/self_projects/prove2me_workspace/.lake/packages/"
$packagePathEntries = @($env:LEAN_PATH -split ";" | Where-Object { $_ -and ([System.IO.Path]::GetFullPath($_).Replace("\", "/").ToLowerInvariant().StartsWith($allowedPackageRoot)) })
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ki1/b/p/lib/lean;" + ($packagePathEntries -join ";")
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ki1"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ki1/b/p/lib/lean/Solutions/Sol_ZetaNine_CoefficientMapKernelBridge_original_quartic_aggregate_kernel_zero.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ki1/Solutions/Sol_ZetaNine_CoefficientMapKernelBridge_original_quartic_aggregate_kernel_zero.lean"
exit $LASTEXITCODE
