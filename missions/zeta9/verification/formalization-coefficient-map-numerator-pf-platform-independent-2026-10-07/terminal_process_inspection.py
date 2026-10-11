"""Own compiler/driver residual check; no external project process management."""
import json, subprocess, sys
import inspect_author as p
sys.stdout.reconfigure(encoding='utf-8')
command=r'''$selected = @(Get-CimInstance Win32_Process | Where-Object { $_.Name -in @('lean.exe','lake.exe','python.exe','pythonw.exe') -and ($_.CommandLine -match 'PFIndependent' -or ($_.CommandLine -match 'formalization-coefficient-map-numerator-pf-platform-independent-2026-10-07' -and $_.CommandLine -match 'run_(phase1|native_control|staged_controls|lossless_encoder|oracles_and_resolvers)')) } | Select-Object ProcessId,Name,CommandLine); ConvertTo-Json -InputObject $selected -Depth 5 -Compress'''
folder=p.OUT/'terminal-process-query';folder.mkdir(exist_ok=True)
result=subprocess.run(['powershell','-NoProfile','-Command',command],capture_output=True)
(folder/'stdout.log').write_bytes(result.stdout);(folder/'stderr.log').write_bytes(result.stderr)
(folder/'exit.txt').write_text(str(result.returncode)+'\n',encoding='ascii')
assert result.returncode==0
rows=json.loads(result.stdout.decode('utf-8-sig'))
assert isinstance(rows,list) and not rows,rows
report=dict(status='ACTUAL_OWN_COMPILER_DRIVER_RESIDUAL_QUERY_ZERO',exit_code=result.returncode,
    matched_processes=rows,matched_count=0,processes_stopped_or_modified=False,
    command=command,source=p.bind(p.OUT/'terminal_process_inspection.py'),
    evidence=[p.bind(folder/name) for name in ['stdout.log','stderr.log','exit.txt']])
(p.OUT/'terminal-process-verification.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('Actual own compiler/driver residual query exit0, matches0.')
