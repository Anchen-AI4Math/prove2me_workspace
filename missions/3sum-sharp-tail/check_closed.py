"""Check selected proved solutions against proof-bearing mirrors of their children.

Original platform reference files remain unchanged. Pass target name suffixes;
the binomial child is compiled into a separate module path before any tail proof.
"""
import importlib.util
import os
from pathlib import Path
import subprocess
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('workspace', ROOT / 'scripts/workspace.py')
workspace = importlib.util.module_from_spec(spec)
spec.loader.exec_module(workspace)


def main():
    lake, base_env = workspace.lake_environment()
    lean_path = subprocess.check_output(
        [lake, 'env', sys.executable, '-c', 'import os; print(os.environ["LEAN_PATH"])'],
        cwd=ROOT, env=base_env, text=True).strip()
    mirror = HERE / 'verification/closed-mirror'
    lib = mirror / 'lib'
    (mirror / 'Theorems').mkdir(parents=True, exist_ok=True)
    (lib / 'Theorems').mkdir(parents=True, exist_ok=True)
    # New bridge proofs use the exact task-local foundation definition closure.
    # Preserve existing closed theorem mirrors when adding these definitions.
    foundation = HERE / 'verification/foundation-mirror/lib/Definitions'
    for child in foundation.rglob('*.olean*'):
        destination = lib / 'Definitions' / child.relative_to(foundation)
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists() or destination.stat().st_mtime != child.stat().st_mtime:
            shutil.copy2(child, destination)
    env = base_env.copy()
    env['LEAN_PATH'] = str(lib) + os.pathsep + lean_path
    lean = str(Path(lake).with_name('lean.exe' if os.name == 'nt' else 'lean'))
    suffixes = sys.argv[1:] or ['binomial_entropy_bounds']
    for suffix in suffixes:
        source = ROOT / f'Solutions/Sol_ThreeSumSharpTail_{suffix}.lean'
        text = source.read_text(encoding='utf-8')
        name = f'ThreeSumSharpTail.{suffix}'
        if text.count('theorem solution') == 1:
            text = text.replace('theorem solution', 'theorem ' + name, 1)
        elif text.count('theorem ' + name + ' ') != 1:
            raise ValueError(f'Expected one solution or exact named theorem in {source}')
        if 'by sorry' in text or 'sorryAx' in text:
            raise ValueError(f'Unclosed source: {source}')
        text = text.replace('#print axioms solution', '#print axioms ' + name)
        if '#print axioms ' + name not in text:
            text += '\n#print axioms ' + name + '\n'
        module = f'Thm_ThreeSumSharpTail_{suffix}'
        path = mirror / 'Theorems' / (module + '.lean')
        path.write_text(text, encoding='utf-8')
        run = subprocess.run([lean, '-R', str(mirror), '-o', str(lib / 'Theorems' / (module + '.olean')),
                              str(path)], cwd=ROOT, env=env, capture_output=True, text=True)
        log = run.stdout + run.stderr
        (HERE / 'verification' / (suffix + '-closed-check.txt')).write_text(log, encoding='utf-8')
        print(log, end='', flush=True)
        if run.returncode or 'sorryAx' in log or 'error:' in log:
            return run.returncode or 1
        reports = [line.split('depends on axioms:', 1)[1].strip()
                   for line in log.splitlines() if 'depends on axioms:' in line]
        if len(reports) != 1:
            raise ValueError('Expected one axiom report for ' + name)
        axioms = {value.strip() for value in reports[0].strip('[]').split(',') if value.strip()}
        if not axioms.issubset({'propext', 'Classical.choice', 'Quot.sound'}):
            raise ValueError('Nonstandard axioms for ' + name + ': ' + repr(axioms))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
