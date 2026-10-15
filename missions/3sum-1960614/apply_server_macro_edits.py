"""Apply parser/macro-produced ranges; keep source and publication history."""
import argparse
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
parser=argparse.ArgumentParser()
parser.add_argument('--first-definition',action='store_true')
args=parser.parse_args()
read=lambda path:json.loads(path.read_text(encoding='utf-8'))
sha=lambda data:hashlib.sha256(data).hexdigest()
manifest_path=VER/'machine-platform-manifest.json'
manifest=read(manifest_path)
hashes=read(VER/'server-macro-input-hashes.json')
state_path=VER/'server-macro-apply-state.json'
state=read(state_path) if state_path.exists() else {'items':{}}
definitions={r['path']:r for r in manifest['definitions']}
theorems={r[k+'_path']:(r,k) for r in manifest['theorems'] for k in ('theorem','solution')}
count=0
lines=(VER/'server-macro-edits.jsonl').read_text(encoding='utf-8').splitlines()
for line in lines:
    item=json.loads(line);rel=item['path']
    if args.first_definition and rel!=manifest['definitions'][0]['path']:continue
    path=ROOT/rel;data=path.read_bytes()
    if rel in state['items']:
        assert sha(data)==state['items'][rel]['result_sha256']
        continue
    assert sha(data)==hashes[rel],('Source changed since parsing',rel)
    ordered=sorted(item['edits'],key=lambda e:(e['start'],e['end']))
    last=0
    for edit in ordered:
        assert last<=edit['start']<=edit['end']<=len(data),('Overlapping parser ranges',rel,edit)
        last=edit['end']
    backup=VER/'server-macro-originals'/rel
    backup.parent.mkdir(parents=True,exist_ok=True)
    if backup.exists():assert backup.read_bytes()==data
    else:backup.write_bytes(data)
    result=data
    for edit in reversed(ordered):
        result=result[:edit['start']]+edit['replacement'].encode()+result[edit['end']:]
    if rel in definitions:
        definitions[rel]['sha256']=sha(result)
    else:
        record,kind=theorems[rel]
        if kind=='theorem':
            assert data==(record['preamble']+'\n'+record['formal_statement']+'\n').encode()
            boundary=len((record['preamble']+'\n').encode())
            assert all(not(e['start']<boundary<e['end']) for e in ordered)
            boundary+=sum(len(e['replacement'].encode())-(e['end']-e['start']) for e in ordered if e['end']<=boundary)
            record['preamble']=result[:boundary-1].decode()
            assert result[boundary-1:boundary]==b'\n' and result.endswith(b'\n')
            record['formal_statement']=result[boundary:-1].decode()
        record[kind+'_sha256']=sha(result)
    path.write_bytes(result)
    state['items'][rel]={'original_sha256':hashes[rel],'result_sha256':sha(result),'parser_edit_count':len(ordered)}
    count+=1
manifest['server_macro_conversion']='Project macros expanded with Lean MacroM/PrettyPrinter; registrations removed; no mathematical declaration elaboration.'
manifest['validation_complete']=False
manifest_path.write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
state.update(updated_at_utc=datetime.now(timezone.utc).isoformat(),applied_file_count=len(state['items']))
state_path.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
print('Applied parser-driven macro conversion to',count,'files;',len(state['items']),'total; no local proof build.')
