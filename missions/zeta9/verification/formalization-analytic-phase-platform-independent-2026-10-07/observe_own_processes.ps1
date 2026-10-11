$taskObservationOut = Split-Path -Parent $MyInvocation.MyCommand.Path
$taskProcessRows = @(Get-CimInstance Win32_Process)
$taskDriverRegex = 'formalization-analytic-phase-platform-independent-2026-10-07[\\/]run_independent[.]py'
$taskOwnRoots = @($taskProcessRows | Where-Object { $_.ProcessId -ne $PID -and $_.CommandLine -match $taskDriverRegex })
$taskOwnIds = [System.Collections.Generic.HashSet[uint32]]::new()
foreach ($taskRow in $taskOwnRoots) { [void]$taskOwnIds.Add([uint32]$taskRow.ProcessId) }
do {
    $taskChanged = $false
    foreach ($taskRow in $taskProcessRows) {
        if ($taskOwnIds.Contains([uint32]$taskRow.ParentProcessId) -and $taskOwnIds.Add([uint32]$taskRow.ProcessId)) { $taskChanged = $true }
    }
} while ($taskChanged)
$taskOwnRows = @($taskProcessRows | Where-Object { $taskOwnIds.Contains([uint32]$_.ProcessId) } | Select-Object ProcessId,ParentProcessId,Name,CreationDate,CommandLine)
$taskNowTag = (Get-Date).ToUniversalTime().ToString('yyyyMMddTHHmmssffffZ')
$taskOutPath = Join-Path $taskObservationOut ('own-process-observation-' + $taskNowTag + '.json')
ConvertTo-Json -InputObject $taskOwnRows -Depth 4 | Set-Content -LiteralPath $taskOutPath -Encoding utf8
Write-Output ('Own process tree snapshot: ' + $taskOwnRows.Count + ' process(es); ' + $taskOutPath)
