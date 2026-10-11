"""Pack, verify and restore large verification records without changing their bytes.

Only explicitly selected missions' untracked data files are eligible for packing.
Packing keeps local originals; restoration never overwrites a different file.
"""
import argparse
import gzip
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = 'archives/verification'
INDEX = f'{ARCHIVE}/index.json'
BEGIN = '# BEGIN workspace_data.py managed paths'
END = '# END workspace_data.py managed paths'


def disk(path):
    """Use extended Windows paths for historical verification directories."""
    path = Path(path).absolute()
    return Path('\\\\?\\' + str(path)) if os.name == 'nt' and not str(path).startswith('\\\\?\\') else path


def inside(root, relative):
    path = PurePosixPath(relative)
    if path.is_absolute() or '..' in path.parts or '\\' in relative or ':' in relative:
        raise ValueError(f'Unsafe archive path: {relative}')
    target = root.joinpath(*path.parts).resolve()
    if not target.is_relative_to(root.resolve()):
        raise ValueError(f'Path outside workspace: {relative}')
    return disk(target)


def fingerprint(path):
    with disk(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def object_path(root, digest):
    if not re.fullmatch('[0-9a-f]{64}', digest):
        raise ValueError('Invalid SHA-256 in archive index')
    return inside(root, f'{ARCHIVE}/objects/{digest}.gz')


def read_index(root):
    path = inside(root, INDEX)
    if not path.exists():
        return []
    data = json.loads(path.read_text(encoding='utf-8'))
    if data.get('schema_version') != 1 or data.get('compression') != 'gzip':
        raise ValueError('Unsupported archive index format')
    entries = data['files']
    names = set()
    for entry in entries:
        name = entry['path']
        if name in names or not name.startswith('missions/'):
            raise ValueError(f'Duplicate or non-mission archive path: {name}')
        names.add(name)
        inside(root, name)
        object_path(root, entry['sha256'])
        if not isinstance(entry['bytes'], int) or entry['bytes'] < 0:
            raise ValueError(f'Invalid byte count: {name}')
    return entries


def unpack_object(root, entry, output=None):
    digest = hashlib.sha256()
    size = 0
    with gzip.open(object_path(root, entry['sha256']), 'rb') as stream:
        while chunk := stream.read(1024 * 1024):
            size += len(chunk)
            if size > entry['bytes']:
                raise ValueError(f'Archive size mismatch: {entry["path"]}')
            digest.update(chunk)
            if output is not None:
                output.write(chunk)
    if size != entry['bytes'] or digest.hexdigest() != entry['sha256']:
        raise ValueError(f'Archive hash/size mismatch: {entry["path"]}')


def verify(root, entries):
    seen = set()
    for entry in entries:
        key = (entry['sha256'], entry['bytes'])
        if key not in seen:
            unpack_object(root, entry)
            seen.add(key)
    print(f'OK: {len(entries)} paths, {len(seen)} compressed objects verified.')


def restore(root, entries):
    # Check every destination before writing any restored file.
    missing = []
    for entry in entries:
        target = inside(root, entry['path'])
        if target.exists():
            if not target.is_file() or fingerprint(target) != entry['sha256']:
                raise ValueError(f'Refusing to overwrite changed file: {entry["path"]}')
        else:
            missing.append(entry)
    verify(root, entries)
    for entry in missing:
        target = inside(root, entry['path'])
        target.parent.mkdir(parents=True, exist_ok=True)
        fd, name = tempfile.mkstemp(prefix='.restore-', dir=target.parent)
        temporary = Path(name)
        try:
            with os.fdopen(fd, 'wb') as output:
                unpack_object(root, entry, output)
            # Exclusive creation also protects against a file appearing mid-restore.
            os.link(temporary, target)
        finally:
            temporary.unlink(missing_ok=True)
    print(f'OK: restored {len(missing)} files; {len(entries) - len(missing)} already match.')


def ignore_line(relative):
    return '/' + ''.join('\\' + c if c in '\\!#[]*? ' else c for c in relative)


def update_ignores(root, entries):
    missions = sorted({entry['path'].split('/')[1] for entry in entries})
    for mission in missions:
        prefix = f'missions/{mission}/'
        path = inside(root, prefix + '.gitignore')
        original = path.read_text(encoding='utf-8') if path.exists() else ''
        if BEGIN in original:
            before, rest = original.split(BEGIN, 1)
            _, after = rest.split(END, 1)
            original = before.rstrip() + '\n' + after.lstrip('\n')
        lines = [ignore_line(entry['path'][len(prefix):]) for entry in entries
                 if entry['path'].startswith(prefix)]
        block = '\n'.join([BEGIN, '# Exact data bytes live in archives/verification; keep local originals.',
                           *sorted(lines), END])
        path.write_text(original.rstrip() + ('\n\n' if original.strip() else '') + block + '\n',
                        encoding='utf-8', newline='\n')


def pack(root, missions, minimum_bytes):
    registry = json.loads(inside(root, 'missions/index.json').read_text(encoding='utf-8'))
    known = {mission['slug'] for mission in registry['missions']}
    if not missions or not set(missions) <= known:
        raise ValueError('Packing requires explicitly selected registered missions')
    entries = read_index(root)
    by_path = {entry['path']: entry for entry in entries}
    files = subprocess.check_output(
        ['git', '-c', 'core.longpaths=true', 'ls-files', '--others', '--exclude-standard', '-z'],
        cwd=root).decode('utf-8').split('\0')
    selected = tuple(f'missions/{mission}/' for mission in missions)
    added = 0
    for name in sorted(files):
        if not name.startswith(selected) or PurePosixPath(name).suffix not in ('.json', '.jsonl', '.bin', ''):
            continue
        source = inside(root, name)
        if not source.is_file() or source.stat().st_size < minimum_bytes:
            continue
        entry = {'path': name, 'bytes': source.stat().st_size, 'sha256': fingerprint(source)}
        destination = object_path(root, entry['sha256'])
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists():
            fd, temporary_name = tempfile.mkstemp(prefix='.pack-', dir=destination.parent)
            temporary = Path(temporary_name)
            try:
                with os.fdopen(fd, 'wb') as output, source.open('rb') as stream:
                    with gzip.GzipFile(filename='', mode='wb', fileobj=output, mtime=0) as compressed:
                        while chunk := stream.read(1024 * 1024):
                            compressed.write(chunk)
                if temporary.stat().st_size >= 90 * 1024 * 1024:
                    raise ValueError(f'Compressed object too large for regular Git: {name}')
                temporary.replace(destination)
            finally:
                temporary.unlink(missing_ok=True)
        unpack_object(root, entry)
        if fingerprint(source) != entry['sha256']:
            raise ValueError(f'File changed while packing: {name}')
        by_path[name] = entry
        added += 1
    entries = sorted(by_path.values(), key=lambda entry: entry['path'])
    index = inside(root, INDEX)
    index.parent.mkdir(parents=True, exist_ok=True)
    index.write_text(json.dumps({'schema_version': 1, 'compression': 'gzip', 'files': entries},
                                ensure_ascii=False, indent=2) + '\n', encoding='utf-8', newline='\n')
    update_ignores(root, entries)
    print(f'Packed {added} new paths; local originals retained.')
    verify(root, entries)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['pack', 'verify', 'restore'])
    parser.add_argument('--mission', action='append', default=[])
    parser.add_argument('--minimum-bytes', type=int, default=1024 * 1024)
    args = parser.parse_args()
    if args.command == 'pack':
        if args.minimum_bytes < 1:
            parser.error('--minimum-bytes must be positive')
        pack(ROOT, args.mission, args.minimum_bytes)
        return
    entries = read_index(ROOT)
    known = {entry['path'].split('/')[1] for entry in entries}
    if set(args.mission) - known:
        parser.error('No archived data for the selected mission')
    if args.mission:
        entries = [entry for entry in entries if entry['path'].split('/')[1] in args.mission]
    (verify if args.command == 'verify' else restore)(ROOT, entries)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError) as exc:
        raise SystemExit(f'ERROR: {exc}') from exc
