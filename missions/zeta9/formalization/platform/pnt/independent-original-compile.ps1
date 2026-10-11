$ErrorActionPreference = 'Stop'
$reviewRoot = 'D:\users\self_projects\prove2me_workspace'
$reviewTask = Join-Path $reviewRoot 'missions\zeta9'
$reviewOutput = Join-Path $reviewTask 'formalization\platform\pnt'
$reviewPntCache = Join-Path $reviewTask 'verification\formalization-pnt-dependency-2026-10-02\project\.lake\build\lib\lean'
$env:LEAN_PATH = $env:LEAN_PATH + [IO.Path]::PathSeparator + $reviewRoot + [IO.Path]::PathSeparator + $reviewPntCache
& lean -o (Join-Path $reviewOutput 'independent-original-PNTTransfer.olean') (Join-Path $reviewTask 'formalization\PNTTransfer.lean') *> (Join-Path $reviewOutput 'independent-original-lean.log')
$reviewCompileExit = $LASTEXITCODE
[IO.File]::WriteAllText((Join-Path $reviewOutput 'independent-original-lean-exit.txt'), "$reviewCompileExit`n", [Text.UTF8Encoding]::new($false))
Write-Output "Independent exact-source PNTTransfer compile exit: $reviewCompileExit"
exit $reviewCompileExit
