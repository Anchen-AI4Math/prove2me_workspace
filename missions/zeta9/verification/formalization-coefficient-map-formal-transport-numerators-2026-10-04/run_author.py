"""Root author lane; explicitly reuse the frozen sixteen parent objects."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys, time

sys.stdout.reconfigure(encoding='utf-8')
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
PROJECT = TASK / '.rt/nu1'
PARENT = TASK / '.rt/ft1'
AUTHOR = TASK / 'verification/formalization-coefficient-map-formal-transport-bounds-2026-10-04'
AUTHOR_SHA = 'e2f3e72b7726cced81edb0e42c578f7015e84e9283af7a32c8e8aba8b3c790e9'
MODULE = 'missions.zeta9.formalization.CoefficientMapFormalTransportNumerators'
SOURCE = TASK / 'formalization/CoefficientMapFormalTransportNumerators.lean'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def write(p, s):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(s if isinstance(s, bytes) else s.encode('utf-8'))
def dump(p, d): write(p, json.dumps(d, ensure_ascii=False, indent=2) + '\n')
def bind(p): return {'root_relative': p.relative_to(ROOT).as_posix(), 'bytes': p.stat().st_size, 'sha256': sha(p)}
def verify(rows):
    for r in rows:
        p = ROOT / r['root_relative']
        assert p.is_file() and p.stat().st_size == r['bytes'] and sha(p) == r['sha256'], str(p)
def author_gate():
    assert sha(AUTHOR / 'author-audit.json') == AUTHOR_SHA
    a = load(AUTHOR / 'author-audit.json')
    assert a['verdict'] == 'PASS' and len(a['stable_files']) == 192
    assert len(a['checks']) == 24 and all(c['pass'] for c in a['checks'])
    verify(a['stable_files'])
    return a
def gate():
    author_gate()
    s = load(OUT / 'preparation-state.json')
    verify(s['parent_sources_and_objects'] + s['copied_bindings'] + s['runtime_bindings'])
    assert (PROJECT / '.lake/packages').is_junction()
    assert (PROJECT / '.lake/packages').resolve() == (ROOT / '.lake/packages').resolve()
    return s
def prepare():
    a = author_gate()
    assert not PROJECT.exists(), 'Fresh short path required; do not overwrite an existing project'
    assert sha(SOURCE) == '28d831023450bd067499b3d57b20b89d38e78e6113b482ad95904962c9920b0f'
    write(PROJECT / 'lakefile.lean', (PARENT / 'lakefile.lean').read_bytes())
    for name in ['lean-toolchain', 'lake-manifest.json']:
        write(PROJECT / name, (ROOT / name).read_bytes())
    packages = PROJECT / '.lake/packages'
    packages.parent.mkdir(parents=True, exist_ok=True)
    r = subprocess.run(['powershell', '-NoProfile', '-Command',
        f"New-Item -ItemType Junction -Path '{packages}' -Target '{ROOT / '.lake/packages'}' | Out-Null"], capture_output=True)
    write(OUT / 'junction.log', r.stdout + r.stderr)
    write(OUT / 'junction-exit.txt', str(r.returncode) + '\n')
    assert r.returncode == 0
    modules = load(AUTHOR / 'preparation-state.json')['parent_modules'] + [
        'missions.zeta9.formalization.CoefficientMapFormalTransportData',
        'missions.zeta9.formalization.CoefficientMapFormalTransportBounds']
    pinned = {r['root_relative']: r for r in a['stable_files']}
    originals, copies = [], []
    for module in modules:
        rel = Path(module.replace('.', '/'))
        paths = [rel.with_suffix('.lean'), Path('b/lib/lean') / rel.with_suffix('.olean')]
        if (PARENT / 'b/lib/lean' / rel.with_suffix('.ilean')).exists():
            paths.append(Path('b/lib/lean') / rel.with_suffix('.ilean'))
        for path in paths:
            p = PARENT / path
            assert p.relative_to(ROOT).as_posix() in pinned, 'Only report-bound parent objects may be reused'
            write(PROJECT / path, p.read_bytes())
            originals.append(bind(p)); copies.append(bind(PROJECT / path))
    assert len(modules) == 16
    dump(OUT / 'preparation-state.json', {
        'author_report_sha256': AUTHOR_SHA, 'parent_modules': modules,
        'parent_sources_and_objects': originals, 'copied_bindings': copies,
        'runtime_bindings': [bind(ROOT / 'lean-toolchain'), bind(ROOT / 'lake-manifest.json'), bind(PROJECT / 'lakefile.lean')],
        'new_project': str(PROJECT), 'reused_parent_objects': 16,
        'fresh_parent_builds_claimed': 0, 'independent_or_Root_proof_objects_borrowed': False,
        'original_uncompiled_candidate': bind(SOURCE),
        'offline_handoff': bind(TASK / 'verification/coefficient-map-formal-transport-numerators-offline-2026-10-04/offline-handoff.json')})
    gate()
    print('Prepared nu1: sixteen explicitly reused and frozen parent objects; zero Lean executions', flush=True)
def run(mode, name):
    gate()
    receipt = OUT / 'actual-execution-receipt.json'
    d = load(receipt) if receipt.exists() else {'rows': [], 'parent_objects_reused_not_fresh': 16}
    folder = OUT / ('e' + str(len(d['rows']) + 1).zfill(2))
    folder.mkdir()
    source = SOURCE if mode == 'compile' else (PROJECT / 'lean-toolchain' if mode == 'runtime' else OUT / name)
    destination = PROJECT / (MODULE.replace('.', '/') + '.lean') if mode == 'compile' else PROJECT / source.name
    write(folder / source.name, source.read_bytes())
    obj = None
    if mode != 'runtime': write(destination, source.read_bytes())
    if mode == 'compile':
        obj = PROJECT / 'b/lib/lean' / (MODULE.replace('.', '/') + '.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        assert len(str(obj)) + 64 <= 259
        command = ['lake', 'env', 'lean', '-o', str(obj), str(destination)]
    elif mode == 'runtime': command = ['lake', 'env', 'lean', '--version']
    else: command = ['lake', 'env', 'lean'] + (['--run'] if mode == 'resolver' else []) + [str(destination)]
    env = dict(os.environ)
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH']: env.pop(key, None)
    env['LEAN_NUM_THREADS'] = '1'; env['LAKE_JOBS'] = '1'
    log = folder / 'run.log'; exitfile = folder / 'exit.txt'
    start = time.monotonic()
    with log.open('wb') as f:
        result = subprocess.run(command, cwd=PROJECT, env=env, stdout=f, stderr=subprocess.STDOUT)
    write(exitfile, str(result.returncode) + '\n')
    row = {'mode': mode, 'name': name, 'actual_exit': result.returncode, 'elapsed_seconds': round(time.monotonic()-start, 3),
        'command': command, 'cwd': str(PROJECT), 'input': bind(folder/source.name), 'log': bind(log), 'exit_file': bind(exitfile),
        'parent_objects_reused_not_fresh': 16, 'independent_objects_borrowed': False, 'Lean_search_path_removed': True}
    if obj is not None and result.returncode == 0:
        write(folder/'compiled.olean', obj.read_bytes()); row['object'] = bind(obj); row['retained_object'] = bind(folder/'compiled.olean')
    d['rows'].append(row); dump(receipt, d)
    gate()
    print(mode, name, 'actual exit', result.returncode, flush=True)
    return result.returncode
if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('mode', choices=['prepare','runtime','compile','audit','resolver'])
    p.add_argument('name', nargs='?', default='CoefficientMapFormalTransportNumerators')
    args = p.parse_args()
    if args.mode == 'prepare': prepare()
    else: raise SystemExit(run(args.mode, args.name))
