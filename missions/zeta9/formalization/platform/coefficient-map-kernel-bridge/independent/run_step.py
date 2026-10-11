"""One serial independent Lean invocation, explicit package-only environment."""
from verify_handoff import *
import subprocess

def rows(path):
    return [json.loads(line) for line in path.read_text(encoding='utf-8-sig').splitlines()
            if line.startswith('{')]

def run(logical, source, cache, output=None, args=None, copy=None):
    verify()
    receipt_path = OUT / 'review-compile-receipt.json'
    receipt = load(receipt_path) if receipt_path.exists() else {
        'complete': False, 'rows': [], 'native_and_staged_objects_borrowed': False,
        'Root_scope_API_credentials_writes': False}
    prior = [r for r in receipt['rows'] if r['logical_step'] == logical]
    if prior:
        assert len(prior) == 1
        r = prior[0]
        assert r['exit_code'] == 0 and r['source_sha256'] == sha(source)
        assert r['cache_task_relative'] == cache.relative_to(TASK).as_posix()
        for key in ['log', 'exit_file', 'wrapper', 'stdout_copy']:
            if r.get(key):
                assert sha(OUT / r[key]) == r[key + '_sha256']
        if output:
            assert sha(output) == r['output_sha256']
        print(logical + ': own identical, hash-bound success reused', flush=True)
        return
    label = 'r' + str(len(receipt['rows']) + 1).zfill(2)
    wrapper = OUT / (label + '.ps1')
    package_root = (ROOT / '.lake/packages').as_posix().lower().rstrip('/') + '/'
    script = '$env:LEAN_NUM_THREADS = "1"\n'
    script += '$allowedPackageRoot = "' + package_root + '"\n'
    script += '$packagePathEntries = @($env:LEAN_PATH -split ";" | Where-Object { $_ -and ([System.IO.Path]::GetFullPath($_).Replace("\\", "/").ToLowerInvariant().StartsWith($allowedPackageRoot)) })\n'
    script += '$env:LEAN_PATH = "' + cache.as_posix() + ';" + ($packagePathEntries -join ";")\n'
    script += 'Set-Location -LiteralPath "' + PROJECT.as_posix() + '"\n& lean '
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        script += '-o "' + output.as_posix() + '" '
    if args is not None:
        script += '--run '
    script += '"' + source.as_posix() + '"'
    script += ''.join(' "' + value + '"' for value in args or []) + '\nexit $LASTEXITCODE\n'
    write(wrapper, script)
    assert len(str(source)) <= 259
    guarded = [wrapper, OUT / (label + '.log'), OUT / (label + '-exit.txt')]
    guarded += [output] if output else []
    guarded += [copy] if copy else []
    assert all(len(str(p)) + 64 <= 259 for p in guarded)
    command = ['lake', 'env', 'pwsh', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', str(wrapper)]
    process = subprocess.run(command, cwd=ROOT, capture_output=True)
    log = OUT / (label + '.log')
    exit_file = OUT / (label + '-exit.txt')
    write(log, process.stdout + process.stderr)
    write(exit_file, str(process.returncode) + '\n')
    if copy:
        write(copy, process.stdout)
    receipt['rows'].append({'label': label, 'logical_step': logical, 'command': command,
        'exit_code': process.returncode, 'source_root_relative': source.relative_to(ROOT).as_posix(),
        'source_sha256': sha(source), 'log': log.name, 'log_sha256': sha(log),
        'exit_file': exit_file.name, 'exit_file_sha256': sha(exit_file),
        'wrapper': wrapper.name, 'wrapper_sha256': sha(wrapper),
        'cache_task_relative': cache.relative_to(TASK).as_posix(),
        'output_task_relative': output.relative_to(TASK).as_posix() if output else None,
        'output_sha256': sha(output) if output and output.exists() else None,
        'stdout_copy': copy.name if copy else None, 'stdout_copy_sha256': sha(copy) if copy else None,
        'lake_env_working_directory': str(ROOT), 'lean_working_directory': str(PROJECT),
        'environment_policy': 'own N/P cache plus fixed Mathlib package caches; no Root proof cache or source fallback'})
    dump(receipt_path, receipt)
    print(logical + ': actual exit ' + str(process.returncode), flush=True)
    verify()
    if process.returncode:
        print(log.read_text(encoding='utf-8-sig'), flush=True)
    assert process.returncode == 0, 'Actual failed source/log/exit retained; no automatic retry'
