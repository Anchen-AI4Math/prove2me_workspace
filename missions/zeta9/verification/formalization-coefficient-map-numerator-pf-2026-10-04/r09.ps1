$env:LEAN_NUM_THREADS="1"
$allowedPackageRoot="d:/users/self_projects/prove2me_workspace/.lake/packages/"
$selected=@($env:LEAN_PATH -split ";" | Where-Object { $_ -and ([System.IO.Path]::GetFullPath($_).Replace("\","/").ToLowerInvariant().StartsWith($allowedPackageRoot)) })
$env:LEAN_PATH="D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/np1/b/lib/lean;"+($selected -join ";")
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/np1"
& lean "D:/users/self_projects/prove2me_workspace/missions/zeta9/verification/formalization-coefficient-map-numerator-pf-2026-10-04/b2.lean"
exit $LASTEXITCODE
