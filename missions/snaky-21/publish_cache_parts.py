"""Publish independent pure cache modules; uses the single locked journal writer."""
import sys
import time
import json
import hashlib
from concurrent.futures import ThreadPoolExecutor
import publish

def part(i,q):
    name=f'Snaky21Calc11Part{i:02}'
    q.THREAD.allowed={'definition:'+name}
    if i:
        while q.read().get('definition:'+f'Snaky21Calc11Part{i-1:02}',{}).get('status')!='PUBLISHED':
            time.sleep(5)
    record=q.read().get('definition:'+name,{})
    if record.get('status')=='PUBLISHED':
        print('REUSE PUBLISHED',name,flush=True)
        return record['theorem_id']
    # Do not replace the source of a server job which is still in progress.
    while record.get('status') in ('PENDING','COMPILING'):
        job=publish.request('GET','/publish-jobs/'+record['job_id'],q.token())
        local=q.read()
        local['definition:'+name].update({'status':job['status'],'theorem_id':job.get('theorem_id'),'error_message':job.get('error_message')})
        q.save(local)
        record=local['definition:'+name]
        if record['status']=='PUBLISHED':
            return record['theorem_id']
        if record['status'] in ('PENDING','COMPILING'):
            time.sleep(10)
    manifest=json.loads((q.OUT/'server-cache-fragments.json').read_text(encoding='utf-8'))
    fragment=manifest.get(str(i))
    if fragment:
        actual=q.ROOT/fragment['actual_file']
        if hashlib.sha256(actual.read_bytes()).hexdigest()!=fragment['actual_sha256']:
            raise RuntimeError('Actual cache module changed after fragment comparison')
        for file in fragment['fragments']:
            path=q.ROOT/file
            q.THREAD.allowed={'definition:'+path.stem.removeprefix('Def_')}
            publish.definition(path,q.token(),q.read())
        q.THREAD.allowed={'definition:'+name}
        return publish.definition(q.ROOT/fragment['wrapper'],q.token(),q.read())
    return publish.definition(q.ROOT/'Definitions'/('Def_'+name+'.lean'),q.token(),q.read())

def main():
    import queue_finish as q
    sys.stdout.reconfigure(encoding='utf-8')
    # The module chain also bounds local Lake memory usage. Publish in that
    # same order; all original literal declarations remain byte-identical.
    for i in range(12):
        part(i,q)
    q.THREAD.allowed={'definition:Snaky21Calc11','definition:Snaky21Catalog'}
    original=q.ROOT/'Definitions'/'Def_Snaky21Calc11.lean'
    server=q.OUT/'Def_Snaky21Calc11.lean'
    server.write_text(original.read_text(encoding='utf-8')+'\nabbrev OAI.Snaky21.Certificate.cache_data_first : OAI.Snaky21.Card := OAI.Snaky21.Certificate.calc11_card_0\n',encoding='utf-8')
    previous=q.read().get('definition:Snaky21Calc11',{})
    if previous.get('status')!='PUBLISHED':
        publish.definition(server,q.token(),q.read())
    else:
        print('REUSE PUBLISHED Snaky21Calc11',flush=True)
    publish.definition(q.ROOT/'Definitions'/'Def_Snaky21Catalog.lean',q.token(),q.read())
    print('Split cache wrapper and catalog definitions published.',flush=True)
    # The already-running finite continuation watches this original phase log.
    with (q.HERE/'verification'/'cache-publish-stdout.log').open('a',encoding='utf-8') as report:
        report.write('\nRESUMED PHASE: Split cache wrapper and catalog definitions published.\n')

if __name__=='__main__':
    main()
