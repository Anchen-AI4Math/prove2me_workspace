"""Read-only exact-name check for every unpublished certificate increment."""
import concurrent.futures
import json
from datetime import datetime,timezone
from urllib.parse import urlencode
import publish

def main():
    token=publish.api.get_token()
    journal=publish.read_journal()
    names=[]
    for path in sorted((publish.HERE/'platform').glob('*.json')):
        spec=json.loads(path.read_text(encoding='utf-8'))
        if isinstance(spec,dict) and 'theorem_name' in spec and 'theorem_id' not in spec:
            name=spec['theorem_name']
            if 'theorem:'+name not in journal:
                names.append(name)
    for path in sorted((publish.ROOT/'Definitions').glob('Def_Snaky21*.lean')):
        name=path.stem.removeprefix('Def_')
        if 'definition:'+name not in journal:
            names.append(name)
    def check(name):
        query=urlencode({'theorem_name':name,'env':publish.ENV,'limit':1})
        result=publish.request('GET','/theorems?'+query,token)
        matches=[{'theorem_id':r['theorem_id'],'status':r['status']} for r in result['theorems']]
        return {'name':name,'matches':matches}
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        rows=list(pool.map(check,names))
    report={'checked_at':datetime.now(timezone.utc).isoformat(),'exact_queries':rows}
    (publish.HERE/'verification'/'exact-name-check.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('Checked',len(rows),'exact unpublished names; matches:',sum(bool(r['matches']) for r in rows))

if __name__=='__main__':
    main()
