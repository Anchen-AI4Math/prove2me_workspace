"""Offline mission navigation and structural checks; never submits proofs."""
import argparse
import ast
import json
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read_scope(slug):
    return json.loads(inside_root(f'missions/{slug}/scope.json').read_text(encoding='utf-8'))


def expand_patterns(patterns):
    result = set()
    for pattern in patterns:
        inside_root(pattern)  # Reject paths escaping the workspace, including symlinks.
        matches = [p for p in ROOT.glob(pattern) if p.is_file()]
        if not matches:
            raise ValueError(f'Scope pattern matches no files: {pattern}')
        for path in matches:
            inside_root(path.relative_to(ROOT))
            result.add(path.relative_to(ROOT).as_posix())
    return sorted(result)


def build_targets(scope):
    # Source paths avoid quoting Lean identifiers such as examples.«two-squares».
    paths = expand_patterns(scope['build'])
    if any(not p.endswith('.lean') for p in paths):
        raise ValueError('Build entries must be Lean source files')
    return paths


def lake_environment():
    env = os.environ.copy()
    toolchain = (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip()
    elan = Path(env.get('ELAN_HOME', Path.home() / '.elan'))
    name = toolchain.replace('/', '--').replace(':', '---')
    bindir = elan / 'toolchains' / name / 'bin'
    native = bindir / ('lake.exe' if os.name == 'nt' else 'lake')
    if native.is_file():
        # Use the already installed pinned toolchain; no elan self-update needed.
        env['PATH'] = str(bindir) + os.pathsep + env.get('PATH', '')
        return str(native), env
    lake = shutil.which('lake')
    if not lake:
        raise ValueError(f'Lake is unavailable; install the pinned toolchain {toolchain}')
    env['ELAN_TOOLCHAIN'] = toolchain
    return lake, env


def build_mission(mission, dry_run=False):
    scope = read_scope(mission['slug'])
    targets = build_targets(scope)
    # Explicit module targets support nested proof libraries on Windows, where
    # Lake does not recognize slash-separated nested source targets.
    if scope.get('module_target_syntax', False):
        targets = ['+' + p[:-5].replace('/', '.') for p in targets]
    if not targets:
        print('No registered build target for this research/maintenance task. See its handoff.')
        return 0
    print(f"{mission['slug']}: {len(targets)} selected root modules (plus their imports)", flush=True)
    if dry_run:
        print('lake build ' + ' '.join(targets))
        return 0
    lake, env = lake_environment()
    return subprocess.run([lake, 'build', *targets], cwd=ROOT, env=env).returncode


def inside_root(value):
    path = (ROOT / value).resolve()
    if not path.is_relative_to(ROOT):
        raise ValueError(f'Path outside workspace: {value}')
    return path


def check(missions):
    errors = []
    slugs = [m['slug'] for m in missions]
    if len(slugs) != len(set(slugs)):
        errors.append('Duplicate mission slugs')
    actual = {p.name for p in (ROOT / 'missions').iterdir()
              if p.is_dir() and not p.name.startswith('_')}
    if actual != set(slugs):
        errors.append(f'Registry/directory mismatch: {sorted(actual ^ set(slugs))}')
    for m in missions:
        for key in ('handoff', 'scratch'):
            if m.get(key) and not inside_root(m[key]).exists():
                errors.append(f"Missing {key}: {m[key]}")
        if f"({m['handoff'].removeprefix('missions/')})" not in (ROOT / 'missions/README.md').read_text(encoding='utf-8'):
            errors.append(f"Missing README handoff: {m['slug']}")
        try:
            scope = read_scope(m['slug'])
            build_targets(scope)
            expand_patterns(scope['sources'])
            expand_patterns(scope.get('papers', []))
            if not inside_root(f"missions/{m['slug']}/AGENTS.md").is_file():
                errors.append(f"Missing agent entry: {m['slug']}")
        except (ValueError, OSError, KeyError) as exc:
            errors.append(f"{m['slug']}: {exc}")
    # New platform solutions must get an explicit task owner instead of silently
    # entering a global default build. Diagnostic certificates are opt-in only.
    owners = {}
    for m in missions:
        try:
            for path in build_targets(read_scope(m['slug'])):
                owners.setdefault(path, []).append(m['slug'])
        except (ValueError, OSError, KeyError):
            pass
    for path in (ROOT / 'Solutions').glob('*.lean'):
        rel = path.relative_to(ROOT).as_posix()
        if path.name == 'SmokeTest.lean' or path.name.startswith('SondowRosserMiddle'):
            continue
        if rel not in owners:
            errors.append(f'Unassigned solution: {rel}; add it to a mission scope.json')
        elif len(owners[rel]) > 1:
            errors.append(f'Duplicate build ownership: {rel}: {owners[rel]}')
    moves = json.loads((ROOT / 'docs/script-migration.json').read_text(encoding='utf-8'))['moves']
    for move in moves:
        if not inside_root(move['to']).is_file() or inside_root(move['from']).exists():
            errors.append(f"Incomplete migration: {move['from']}")
    sources = list((ROOT / 'scripts').glob('*.py'))
    sources += list((ROOT / 'missions').glob('*/scripts/*.py'))
    for path in sources:
        try:
            ast.parse(path.read_text(encoding='utf-8-sig'), filename=str(path))
        except SyntaxError as exc:
            errors.append(str(exc))
    for error in errors:
        print(f'ERROR: {error}')
    if not errors:
        print(f'OK: {len(missions)} workstreams, {len(moves)} moved scripts, {len(sources)} Python files parsed.')
    return bool(errors)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    commands.add_parser('list')
    show = commands.add_parser('show')
    show.add_argument('slug')
    files = commands.add_parser('files', help='List only the selected mission source scope')
    files.add_argument('slug')
    build = commands.add_parser('build', help='Build a mission and its actual Lean imports only')
    build.add_argument('slug')
    build.add_argument('--dry-run', action='store_true')
    commands.add_parser('check')
    args = parser.parse_args()
    missions = json.loads((ROOT / 'missions/index.json').read_text(encoding='utf-8'))['missions']
    if args.command == 'check':
        return check(missions)
    if args.command == 'list':
        for m in missions:
            print(f"{m['slug']:25} {m['family']:15} {m['title']}")
        return 0
    m = next((m for m in missions if m['slug'] == args.slug), None)
    if m is None:
        parser.error(f'Unknown mission: {args.slug}')
    if args.command == 'build':
        return build_mission(m, args.dry_run)
    if args.command == 'files':
        print('\n'.join(expand_patterns(read_scope(m['slug'])['sources'])))
        return 0
    print(m['title'])
    print(f"Handoff: {m['handoff']}")
    print(f"Scratch: {m.get('scratch') or '(see handoff)'}")
    print(f"Agent entry: missions/{m['slug']}/AGENTS.md")
    print(f"Build: python scripts/workspace.py build {m['slug']}")
    print(f"Sources: python scripts/workspace.py files {m['slug']}")
    for paper_index in read_scope(m['slug']).get('papers', []):
        print(f'Papers: {paper_index}')
    print('Scripts (inspect before running; some perform platform writes):')
    for path in sorted((ROOT / 'missions' / m['slug'] / 'scripts').glob('*')):
        if path.is_file():
            print(f'  {path.relative_to(ROOT).as_posix()}')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, OSError, KeyError) as exc:
        raise SystemExit(f'ERROR: {exc}') from exc
