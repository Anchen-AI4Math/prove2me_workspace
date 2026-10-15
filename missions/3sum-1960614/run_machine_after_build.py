"""Supervised continuation: successful scoped build -> exact CI gates -> metadata.

Pin the live Windows build process handle and current manifest. A failed build
or any manifest edit aborts this continuation; it never restarts compilation,
publishes content, or treats a partial batch as success.
"""
import argparse
import ctypes
from ctypes import wintypes
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
parser = argparse.ArgumentParser()
parser.add_argument('--pid', type=int, required=True)
args = parser.parse_args()
manifest_path = VER / 'machine-platform-manifest.json'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest_sha = sha(manifest_path)
assert os.name == 'nt'
kernel = ctypes.WinDLL('kernel32', use_last_error=True)
kernel.OpenProcess.argtypes = (wintypes.DWORD, wintypes.BOOL, wintypes.DWORD)
kernel.OpenProcess.restype = wintypes.HANDLE
kernel.WaitForSingleObject.argtypes = (wintypes.HANDLE, wintypes.DWORD)
kernel.WaitForSingleObject.restype = wintypes.DWORD
kernel.GetExitCodeProcess.argtypes = (wintypes.HANDLE, ctypes.POINTER(wintypes.DWORD))
kernel.GetExitCodeProcess.restype = wintypes.BOOL
kernel.CloseHandle.argtypes = (wintypes.HANDLE,)
handle = kernel.OpenProcess(0x100000 | 0x1000, False, args.pid)
if not handle:
    raise ctypes.WinError(ctypes.get_last_error())
print('Pinned build process', args.pid, '; waiting for its actual exit.', flush=True)
try:
    while True:
        status = kernel.WaitForSingleObject(handle, 1000)
        assert sha(manifest_path) == manifest_sha, 'Manifest changed; continuation cancelled'
        if status == 0:
            break
        assert status == 258, ('Unexpected process wait status', status)
    exit_code = wintypes.DWORD()
    if not kernel.GetExitCodeProcess(handle, ctypes.byref(exit_code)):
        raise ctypes.WinError(ctypes.get_last_error())
    assert exit_code.value == 0, ('Scoped build failed; no later gate executed', exit_code.value)
finally:
    kernel.CloseHandle(handle)
log = (VER / 'machine-platform-build.txt').read_text(encoding='utf-8', errors='replace')
batches = re.findall(r'Scoped build batch (\d+)/(\d+):', log)
assert batches and int(batches[-1][0]) == int(batches[-1][1])
assert log.count('Build completed successfully') >= int(batches[-1][1])
assert not re.search(r'^error:', log, re.M)
build_receipt={'checked_at_utc':datetime.now(timezone.utc).isoformat(),
               'manifest_sha256':manifest_sha,'process_id':args.pid,'exit_code':0,
               'all_scoped_batches_passed':True,'batch_count':int(batches[-1][1]),
               'log_sha256':sha(VER/'machine-platform-build.txt')}
(VER/'machine-scoped-build-validation.json').write_text(json.dumps(build_receipt,indent=2)+'\n',encoding='utf-8')
env = os.environ.copy()
env['LEAN_NUM_THREADS'] = '1'


def run(script, *arguments):
    assert sha(manifest_path) == manifest_sha, 'Manifest changed during continuation'
    result = subprocess.run([sys.executable, str(HERE / script), *arguments], cwd=ROOT, env=env)
    assert result.returncode == 0, (script, result.returncode)


print('All scoped build batches passed; starting exact compiled CI gates.', flush=True)
run('prepare_batch_solution_types.py')
run('run_machine_type_checks.py', '--compiled-solutions')
frozen = json.loads((VER / 'machine-frozen-bridge-type.json').read_text(encoding='utf-8'))
stubs = json.loads((VER / 'machine-platform-types-stubs.json').read_text(encoding='utf-8'))
bridge = next(r for r in stubs if r['name'] == 'ThreeSum1960614.costs_solve_3sum')
for key in ('universeCount', 'normalizedType'):
    assert bridge[key] == frozen[key], ('Frozen bridge contract differs', key)
receipt = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
           'manifest_sha256': manifest_sha, 'frozen_root_contract_passed': True,
           'evidence_sha256': {name: sha(VER / name) for name in
                              ('machine-frozen-bridge-type.json', 'machine-platform-types-stubs.json',
                               'machine-platform-type-validation.json')}}
(VER / 'machine-frozen-bridge-validation.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
run('prepare_machine_metadata_batches.py')
print('Full local build/types/frozen bridge passed; metadata batches ready. Publication remains pending.', flush=True)
