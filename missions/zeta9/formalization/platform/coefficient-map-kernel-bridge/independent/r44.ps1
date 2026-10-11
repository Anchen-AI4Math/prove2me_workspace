$env:LEAN_NUM_THREADS = "1"
$allowedPackageRoot = "d:/users/self_projects/prove2me_workspace/.lake/packages/"
$packagePathEntries = @($env:LEAN_PATH -split ";" | Where-Object { $_ -and ([System.IO.Path]::GetFullPath($_).Replace("\", "/").ToLowerInvariant().StartsWith($allowedPackageRoot)) })
$env:LEAN_PATH = "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ki1/b/n/lib/lean;" + ($packagePathEntries -join ";")
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ki1"
& lean --run "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-kernel-bridge/independent/parse-NativeKernelIndependentControl.lean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/ki1/NativeKernelIndependentControl.lean" "ZetaNine"
exit $LASTEXITCODE
