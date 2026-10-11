$env:LEAN_NUM_THREADS="1"
$allowedPackageRoot="d:/users/self_projects/prove2me_workspace/.lake/packages/"
$selected=@($env:LEAN_PATH -split ";" | Where-Object { $_ -and ([System.IO.Path]::GetFullPath($_).Replace("\","/").ToLowerInvariant().StartsWith($allowedPackageRoot)) })
$env:LEAN_PATH="D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/np1/b/lib/lean;"+($selected -join ";")
Set-Location -LiteralPath "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/np1"
& lean -o "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/np1/b/lib/lean/missions/zeta9/formalization/CoefficientMapFormalTransportData.olean" "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/np1/missions/zeta9/formalization/CoefficientMapFormalTransportData.lean"
exit $LASTEXITCODE
