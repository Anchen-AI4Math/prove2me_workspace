$ErrorActionPreference = 'Stop'
$reviewOut = $PSScriptRoot
$targetPid = 66984
$cpuCap = 1200.0
$observations = [System.Collections.Generic.List[object]]::new()
$resultPath = Join-Path $reviewOut 'r23-resource-cap-receipt.json'
while ($true) {
    $cim = Get-CimInstance Win32_Process -Filter "ProcessId = $targetPid" | Select-Object -First 1
    if ($null -eq $cim) {
        $outcome = 'original Lean process terminated normally or externally before this monitor enforced its cap'
        break
    }
    if ($cim.Name -ne 'lean.exe' -or $cim.CommandLine -notlike '*ni1*IndependentSourceGraphV2.lean*') {
        throw 'Exact r23 Lean command-line identity no longer matches; no process was stopped'
    }
    $process = Get-Process -Id $targetPid
    $row = [ordered]@{
        observed_at = [DateTimeOffset]::UtcNow.ToString('o')
        pid = $targetPid
        command_line = $cim.CommandLine
        cpu_seconds = $process.CPU
        working_set_bytes = $process.WorkingSet64
        started_at = $process.StartTime.ToUniversalTime().ToString('o')
    }
    $observations.Add($row)
    $row | ConvertTo-Json -Compress | Write-Output
    if ($process.CPU -ge $cpuCap) {
        Stop-Process -Id $targetPid -Force
        $outcome = 'explicit Root resource cap reached; exact verified r23 Lean process intentionally interrupted; no PASS result'
        break
    }
    Start-Sleep -Seconds 15
}
[ordered]@{
    authorization = 'Root explicitly authorized a1200 CPU-second cap after a verified925 CPU-second zero-output observation'
    cpu_cap_seconds = $cpuCap
    exact_target_pid = $targetPid
    outcome = $outcome
    observations = $observations
    author_or_proof_source_modified = $false
    new_Lean_process_started_by_monitor = $false
} | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath $resultPath -Encoding utf8
