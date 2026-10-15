"""Prepare the skill's metadata batches only after the full exact-type gate."""
import hashlib
import json
from pathlib import Path
import argparse

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
manifest_path = VER / 'machine-platform-manifest.json'
manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
parser=argparse.ArgumentParser()
parser.add_argument('--server-first',action='store_true')
args=parser.parse_args()
assert not manifest['regression_only']
if args.server_first:
    authorization=json.loads((VER/'machine-server-first-authorization.json').read_text(encoding='utf-8'))
    assert authorization['user_authorized_server_compilation']
    assert authorization['manifest_sha256']==hashlib.sha256(manifest_path.read_bytes()).hexdigest()
    for theorem in manifest['theorems']:
        for key in ('theorem','solution'):
            assert hashlib.sha256((ROOT/theorem[key+'_path']).read_bytes()).hexdigest()==theorem[key+'_sha256']
else:
    validation = json.loads((VER / 'machine-platform-type-validation.json').read_text(encoding='utf-8'))
    assert validation['manifest_sha256'] == hashlib.sha256(manifest_path.read_bytes()).hexdigest()
    assert validation['exact_types_equal_after_explicit_relocation'] and validation['all_exit_codes_zero']
types = {r['name']: r for r in json.loads((VER / 'machine-platform-types-native.json').read_text(encoding='utf-8'))}
items = []
for theorem in manifest['theorems']:
    items.append({'kind': 'theorem', 'name': theorem['name'],
                  'original_decl': theorem['original_decl'], 'source': theorem['source'],
                  'formal_statement': theorem['formal_statement'],
                  'original_type': types[theorem['original_decl']]['printedType'],
                  'children': theorem['children']})
for definition in manifest['definitions']:
    path = ROOT / definition['path']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == definition['sha256']
    items.append({'kind': 'definition', 'name': definition['module'].removeprefix('Definitions.Def_'),
                  'original_modules': definition.get('original_modules', [definition['original_module']]),
                  'code': path.read_text(encoding='utf-8'), 'path': definition['path']})
if args.server_first:items.sort(key=lambda item:item['kind']!='definition')
destination = HERE / 'metadata' / 'machine-batches'
destination.mkdir(parents=True, exist_ok=True)
index = []
instructions = (
    'Draft metadata only; never edit Lean code, mathematical scope, names or source links. '
    'Return a JSON array with one entry for each input name. Each theorem needs theorem_title, '
    'natural_language_statement, tags and explanation. Each definition needs definition_title, '
    'natural_language_statement and tags. Write academic English with valid KaTeX, explain every '
    'variable and hypothesis, include the main formula where useful, and add a role paragraph in '
    'the complete deterministic integer 3SUM runtime proof. A Lean dump or generic upload notice '
    'is not an explanation. Preserve attribution and distinguish the independent fixed-model '
    'bound from a universal 3SUM lower bound. Use the common tag 3sum-1960614. Do not claim a new '
    'speed record or priority. Read references/contribute.md for contributor principles.')
batches=[]
for item in items:
    size=len(json.dumps(item,ensure_ascii=False))
    maximum=5 if item['kind']=='definition' else 25
    if (not batches or batches[-1][0]['kind']!=item['kind'] or len(batches[-1])>=maximum
            or sum(len(json.dumps(x,ensure_ascii=False)) for x in batches[-1])+size>120000):
        batches.append([])
    batches[-1].append(item)
for batch,selected in enumerate(batches,1):
    path = destination / ('input-' + str(batch).zfill(3) + '.json')
    payload = {'instructions': instructions, 'batch': batch, 'items': selected,
               'source_repository': manifest['source_repository'], 'source_commit': manifest['source_commit']}
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    index.append({'batch': batch, 'input': path.relative_to(ROOT).as_posix(),
                  'names': [item['name'] for item in payload['items']],
                  'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
(destination / 'index.json').write_text(json.dumps(index, indent=2) + '\n', encoding='utf-8')
print('Prepared',len(index),'metadata batches for',len(items),
      'source-reviewed items; server-first =' if args.server_first else 'locally validated items;',args.server_first)
