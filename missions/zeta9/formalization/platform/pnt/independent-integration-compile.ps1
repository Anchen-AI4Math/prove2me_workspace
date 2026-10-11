$ErrorActionPreference = 'Stop'
$taskOut = $PSScriptRoot
$taskRoot = (Resolve-Path (Join-Path $taskOut '../../..')).Path
$repoRoot = (Resolve-Path (Join-Path $taskRoot '../..')).Path
$actualPnt = Join-Path $taskRoot 'verification/formalization-pnt-dependency-2026-10-02/project/.lake/build/lib/lean'
$nativeMirror = Join-Path $taskOut 'build/native'
$source = Join-Path $taskOut 'staged/Solutions/Sol_ZetaNine_HarmonicStability_harmonic_perturbed_log_den_rate.lean'
$output = Join-Path $taskOut 'independent-native-perturbed.olean'
$before = (Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash.ToLowerInvariant()
$env:LEAN_PATH = "$nativeMirror;" + $env:LEAN_PATH + ";$repoRoot;$actualPnt"
Set-Location -LiteralPath (Join-Path $taskOut 'staged')
& lean -o $output $source
$compileExit = $LASTEXITCODE
$after = (Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash.ToLowerInvariant()
if ($before -ne $after) { throw 'Canonical Solution changed during the independent compile.' }
[System.IO.File]::WriteAllText((Join-Path $taskOut 'independent-native-perturbed-exit.txt'), "$compileExit`n", [System.Text.UTF8Encoding]::new($false))
exit $compileExit
