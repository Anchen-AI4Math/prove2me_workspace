"""Check one bridge proof against exact foundation definitions and closed children."""
import importlib.util
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('workspace', ROOT / 'scripts/workspace.py')
workspace = importlib.util.module_from_spec(spec)
spec.loader.exec_module(workspace)
lake, base = workspace.lake_environment()
paths = subprocess.check_output([lake, 'env', sys.executable, '-c',
    'import os; print(os.environ["LEAN_PATH"])'], cwd=ROOT, env=base, text=True).strip()
env = base.copy()
# Lean resolves the first package directory, so merge the two task mirrors.
lib = HERE / 'verification/bridge-lib'
artifacts = {}
for tree in [HERE / 'verification/foundation-mirror/lib', HERE / 'verification/closed-mirror/lib']:
    for src in tree.rglob('*.olean*'):
        artifacts[src.relative_to(tree)] = src
# Select the final layer before copying. Rewriting an identical foundation
# artifact and then its closed counterpart can fail on Windows while another
# Lean process maps it. Equal content needs no write, even with different mtimes.
for relative, src in artifacts.items():
    dst = lib / relative
    dst.parent.mkdir(parents=True, exist_ok=True)
    if not dst.exists() or dst.read_bytes() != src.read_bytes():
        shutil.copy2(src, dst)
env['LEAN_PATH'] = str(lib) + os.pathsep + paths
lean = str(Path(lake).with_name('lean.exe'))
path = Path(sys.argv[1]).resolve()
if not path.is_relative_to(ROOT):
    raise ValueError('The bridge proof must be in this workspace')
log_path = HERE / 'verification' / (path.stem + '-check.txt')
# Keep diagnostics readable while Lean is running. In particular, a long
# proof should not look silent merely because subprocess.run buffers stdout.
with log_path.open('w', encoding='utf-8') as log:
    run = subprocess.Popen([lean, str(path)], cwd=ROOT, env=env,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, encoding='utf-8', errors='replace', bufsize=1)
    for line in run.stdout:
        log.write(line)
        log.flush()
        if any(marker in line for marker in
                (': error', 'PANIC', 'depends on axioms:', 'checkpoint:')):
            print(line, end='', flush=True)
    code = run.wait()
print('Lean check exit ' + str(code) + '; full log: ' + str(log_path), flush=True)
raise SystemExit(code)
