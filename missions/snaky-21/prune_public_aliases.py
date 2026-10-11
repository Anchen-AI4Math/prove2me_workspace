"""Remove unused projection declarations from unaccepted proof adapters only."""
import json
import re
from pathlib import Path

HERE=Path(__file__).resolve().parent
OUT=HERE/'platform'
ROOT=HERE.parents[1]
ALIAS=re.compile(r'^theorem (valid_\d+) : Valid card_\d+ := block[^\n]+\n',re.M)

def main():
    journal=json.loads((OUT/'journal.json').read_text(encoding='utf-8'))
    changed=[]
    for path in sorted(OUT.glob('block*-part*-proof.lean')):
        spec=json.loads(path.with_name(path.name.replace('-proof.lean','.json')).read_text(encoding='utf-8'))
        record=journal.get('proof:'+spec['theorem_name'],{})
        if record.get('status') in ('ACCEPTED','PENDING','SKETCH_ACCEPTED'):
            continue
        code=path.read_text(encoding='utf-8')
        body=ALIAS.sub('',code)
        used=set(re.findall(r'\bvalid_\d+\b',body))
        result=ALIAS.sub(lambda m:m.group(0) if m.group(1) in used else '',code)
        if result!=code:
            path.write_text(result,encoding='utf-8')
            changed.append({'file':str(path.relative_to(ROOT)), 'removed_aliases':len(ALIAS.findall(code))-len(ALIAS.findall(result))})
    (HERE/'verification'/'pruned-adapters.json').write_text(json.dumps(changed,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(changed,indent=2))

if __name__=='__main__':
    main()
