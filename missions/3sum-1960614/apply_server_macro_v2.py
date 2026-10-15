"""Reconstruct hygienic plain Lean source; preserve all publication receipts."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
read = lambda p: json.loads(p.read_text(encoding='utf-8'))
sha = lambda b: hashlib.sha256(b).hexdigest()
manifest_path = VER / 'machine-platform-manifest.json'
manifest = read(manifest_path)
published = read(VER / 'machine-platform-publish.json')['items']
definitions = {r['path']: r for r in manifest['definitions']}
theorems = {r[k + '_path']: (r, k) for r in manifest['theorems'] for k in ('theorem', 'solution')}
hashes = read(VER / 'server-macro-input-hashes.json')
macro_path = VER / 'server-macro-apply-state.json'
macro_state = read(macro_path)
imports = read(VER / 'server-import-apply-state.json')['imports']
facade = b'import Submission.ThreeSumApsp.Util.Basic\n'
plain_imports = ('\n'.join('import ' + m for m in imports) + '\n').encode()
raw = (VER / 'server-macro-edits-v2.jsonl').read_text(encoding='utf-8')
# The converter flushes one complete JSON record per line. Do not use a partial write.
lines = raw.splitlines() if raw.endswith('\n') else raw.splitlines()[:-1]
changed = 0
for line in lines:
    item = json.loads(line)
    rel = item['path']
    original = (VER / 'server-macro-originals' / rel).read_bytes()
    assert sha(original) == hashes[rel]
    edits = sorted(item['edits'], key=lambda e: (e['start'], e['end']))
    # Each expansion is wrapped in one additional pair of parentheses by the
    # converter. Move continuation lines one column right as well, preserving
    # the formatter's relative tactic indentation after that opening token.
    edits = [{**e, 'replacement': e['replacement'].replace('\n', '\n ')} for e in edits]
    last = 0
    for e in edits:
        assert last <= e['start'] <= e['end'] <= len(original)
        assert '\u271d' not in e['replacement'], ('Inaccessible printed identifier', rel)
        last = e['end']
    result = original
    for e in reversed(edits):
        result = result[:e['start']] + e['replacement'].encode() + result[e['end']:]
    result = result.replace(facade, plain_imports)
    path = ROOT / rel
    current = path.read_bytes()
    if rel in definitions:
        record = definitions[rel]
        name = record['module'].removeprefix('Definitions.Def_')
        if published.get(name, {}).get('theorem_id'):
            assert [l for l in current.splitlines() if l.strip()] == [l for l in result.splitlines() if l.strip()], ('Published definition would change', name)
            # Retain the exact accepted bytes, including the manual Bundle001
            # blank-line layout, rather than touching a published statement.
            result = current
        record['sha256'] = sha(result)
    else:
        record, kind = theorems[rel]
        p = published.get(record['name'], {})
        if kind == 'theorem':
            matches = list(re.finditer(rb'(?m)^theorem ' + re.escape(record['name'].encode()) + rb'(?=[\s.{(:])', original))
            assert len(matches) == 1, ('Cannot identify original target boundary', rel)
            boundary = matches[0].start()
            assert all(not (e['start'] < boundary < e['end']) for e in edits)
            boundary += sum(len(e['replacement'].encode()) - e['end'] + e['start'] for e in edits if e['end'] <= boundary)
            boundary += original[:matches[0].start()].count(facade) * (len(plain_imports) - len(facade))
            assert result[boundary - 1:boundary] == b'\n' and result.endswith(b'\n')
            if p.get('theorem_id') and not record.get('existing_theorem_id'):
                assert current == result, ('Published theorem would change', record['name'])
            record['preamble'] = result[:boundary - 1].decode()
            record['formal_statement'] = result[boundary:-1].decode()
        elif p.get('proof_status') == 'ACCEPTED':
            assert current == result, ('Accepted proof would change', record['name'])
        record[kind + '_sha256'] = sha(result)
    if current != result:
        backup = VER / 'server-macro-v1-rendered' / rel
        backup.parent.mkdir(parents=True, exist_ok=True)
        if not backup.exists():
            backup.write_bytes(current)
        path.write_bytes(result)
        changed += 1
    macro_state['items'][rel].update(result_sha256=sha(result), macro_render_version=3)
manifest['server_macro_conversion'] = 'Lean MacroM expansion with explicit global names and fresh ordinary local identifiers; no mathematical elaboration.'
manifest['validation_complete'] = False
manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
macro_state['updated_at_utc'] = datetime.now(timezone.utc).isoformat()
macro_path.write_text(json.dumps(macro_state, indent=2) + '\n', encoding='utf-8')
print('Applied hygienic plain-source rendering to', len(lines), 'files;', changed, 'changed; no proof compilation.')
