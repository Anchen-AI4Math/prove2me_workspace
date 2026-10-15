"""Compile fetched definition dependencies in the task-local mirror only."""
import importlib.util
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MIRROR = HERE / 'verification/foundation-mirror'
spec = importlib.util.spec_from_file_location('workspace', ROOT / 'scripts/workspace.py')
workspace = importlib.util.module_from_spec(spec)
spec.loader.exec_module(workspace)


def main():
    lake, base = workspace.lake_environment()
    lean_path = subprocess.check_output([lake, 'env', sys.executable, '-c',
        'import os; print(os.environ["LEAN_PATH"])'], cwd=ROOT, env=base, text=True).strip()
    lib = MIRROR / 'lib'
    env = base.copy()
    env['LEAN_PATH'] = str(lib) + os.pathsep + lean_path
    lean = str(Path(lake).with_name('lean.exe'))
    seen = set()

    def build(module):
        if module in seen:
            return
        seen.add(module)
        rel = Path(*module.split('.')).with_suffix('.lean')
        path = MIRROR / rel
        if not path.exists():
            if (ROOT / rel).exists():
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text((ROOT / rel).read_text(encoding='utf-8'), encoding='utf-8')
            else:
                raise RuntimeError('Missing fetched module: ' + module)
        text = path.read_text(encoding='utf-8')
        for child in re.findall(r'^\s*(?:public\s+)?import\s+((?:Definitions|Theorems)\.\S+)\s*$', text, re.M):
            build(child)
        output = (lib / rel).with_suffix('.olean')
        if output.exists() and output.stat().st_mtime >= path.stat().st_mtime:
            return
        output.parent.mkdir(parents=True, exist_ok=True)
        print('Compiling ' + module, flush=True)
        run = subprocess.run([lean, '-R', str(MIRROR), '-o', str(output), str(path)],
                             cwd=ROOT, env=env, capture_output=True, text=True)
        log = run.stdout + run.stderr
        (MIRROR / (module + '-build.txt')).write_text(log, encoding='utf-8')
        if run.returncode:
            print(log, flush=True)
            raise RuntimeError('Compile failed: ' + module)

    for module in sys.argv[1:]:
        build(module)
    print('Requested definition modules compiled.', flush=True)


if __name__ == '__main__':
    main()
