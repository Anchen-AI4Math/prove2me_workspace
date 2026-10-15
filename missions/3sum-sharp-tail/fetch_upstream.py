"""Read a named dependency source from the pinned upstream commit."""
from pathlib import Path
import argparse
import re
import sys
import urllib.request

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--commit', default='e1a4e6508154ea59f030480661590a9fe3018011')
parser.add_argument('sources', nargs='+')
args = parser.parse_args()
COMMIT = args.commit
if not re.fullmatch(r'[0-9a-f]{12,40}', COMMIT):
    raise SystemExit('Use the exact pinned commit hash or its known unique prefix')
BASE = 'https://raw.githubusercontent.com/anthropics/formal-math/' + COMMIT + '/3sum-apsp/'
opener = urllib.request.build_opener(urllib.request.ProxyHandler({
    'https': 'http://127.0.0.1:65532', 'http': 'http://127.0.0.1:65532'}))
for name in args.sources:
    rel = Path(name)
    if rel.is_absolute() or '..' in rel.parts or not name.endswith('.lean'):
        raise SystemExit('Pass a repository-relative .lean source path')
    directory = 'upstream' if COMMIT == 'e1a4e6508154ea59f030480661590a9fe3018011' else 'upstream-' + COMMIT
    target = HERE / 'verification' / directory / rel
    with opener.open(BASE + name.replace('\\', '/'), timeout=120) as response:
        text = response.read().decode('utf-8')
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text, encoding='utf-8')
    print(name + f': {len(text)} chars', flush=True)
