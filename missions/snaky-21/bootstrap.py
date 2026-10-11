"""Fetch exact mission source and the pinned, relevant paper supplement."""
import hashlib
import json
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
import p2m_api as api

PIN = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
BASE = f'https://raw.githubusercontent.com/openai/math/{PIN}/preprints/Snaky-in-21-Maker-moves-September-25-2026/'

def main():
    token = api.get_token()
    records = {}
    for label, target in [('target', '29b16242-e6c3-4ee3-b459-3e4a883b9dcc'), ('definition', '9aa200b0-5e32-4b9f-bc67-389947c5b047')]:
        status, body = api._request('GET', '/theorems/' + target, token=token)
        if status != 200:
            raise RuntimeError(f'{label}: HTTP {status}')
        records[label] = json.loads(body)
    (HERE / 'platform').mkdir(exist_ok=True)
    (HERE / 'platform' / 'initial.json').write_text(json.dumps(records, ensure_ascii=False, indent=2), encoding='utf-8')
    (ROOT / 'Definitions' / 'Def_SnakyTwentyOne.lean').write_text(records['definition']['definition'], encoding='utf-8')
    source_files = ['README.md', 'build/templates.tex', 'build/strategy.tex', 'build/certificate-proof.tex', 'verification/verify_certificate.py', 'verification/certificate.txt', 'verification/supporting/independent_evaluator.py']
    hashes = {}
    for rel in source_files:
        with urllib.request.urlopen(BASE + rel, timeout=30) as response:
            payload = response.read()
        dest = HERE / 'source' / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(payload)
        hashes[rel] = hashlib.sha256(payload).hexdigest()
    assert hashes['verification/certificate.txt'] == '3fa12d36a6d4dbb185e3f2808c8dfde13d85ee309afbca030d6ad17ae9fe3d04'
    (HERE / 'source' / 'manifest.json').write_text(json.dumps({'commit': PIN, 'sha256': hashes}, indent=2), encoding='utf-8')
    registry = ROOT / 'missions' / 'index.json'
    index = json.loads(registry.read_text(encoding='utf-8'))
    if not any(m['slug'] == 'snaky-21' for m in index['missions']):
        index['missions'].append({'slug': 'snaky-21', 'title': 'Snaky in 21 Maker moves', 'family': 'combinatorics', 'handoff': 'missions/snaky-21/status.md', 'scratch': None})
        registry.write_text(json.dumps(index, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    navigation = ROOT / 'missions' / 'README.md'
    text = navigation.read_text(encoding='utf-8')
    row = '| combinatorics | [Snaky in 21 Maker moves](snaky-21/status.md) | [snaky-21](snaky-21/AGENTS.md) |\n'
    if '(snaky-21/status.md)' not in text:
        text = text.replace('\n平台状态', '\n' + row + '\n平台状态')
        navigation.write_text(text, encoding='utf-8')
    print('Pinned sources and exact platform definition saved; Snaky task registered.')

if __name__ == '__main__':
    main()
