"""Four platform API workers, one merged journal, and zero local Lean jobs."""
import json
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor
import queue_finish as q
import publish
import remote_milestones as remote
from submit_milestone import SPECS

HERE=q.HERE
ROOT=q.ROOT

def imports(source):
    return re.findall(r'^import\s+(\S+)',source,re.M)

def worker(slug,spec):
    name=spec['theorem_name']
    q.THREAD.allowed={'theorem:'+name,'proof:'+name}
    result=publish.lemma(HERE/'platform'/(slug+'.json'),q.token(),q.read())
    if result['status']!='ACCEPTED':
        raise RuntimeError('A support is not fully ACCEPTED: '+name)
    print('REMOTE ACCEPTED',slug,flush=True)
    return slug

def statement_worker(slug,spec):
    q.THREAD.allowed={'theorem:'+spec['theorem_name']}
    publish.statement(HERE/'platform'/(slug+'.json'),q.token(),q.read())
    print('REMOTE STATEMENT READY',slug,flush=True)
    return slug

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    manifest=json.loads((HERE/'platform'/'milestone35-manifest.json').read_text(encoding='utf-8'))
    slugs=[manifest['lookup']]
    for parent in manifest['parts']:
        slugs.extend(manifest['subparts'][parent])
        slugs.append(parent)
    specs={s:json.loads((HERE/'platform'/(s+'.json')).read_text(encoding='utf-8')) for s in slugs}
    by_module={'Theorems.Thm_'+obj['theorem_name'].replace('.','_'):s for s,obj in specs.items()}
    deps={s:{by_module[m] for m in imports((ROOT/specs[s]['proof_file']).read_text(encoding='utf-8')) if m in by_module} for s in slugs}
    done={s for s in slugs if q.read().get('proof:'+specs[s]['theorem_name'],{}).get('status')=='ACCEPTED'}
    stated={s for s in slugs if q.read().get('theorem:'+specs[s]['theorem_name'],{}).get('status')=='PUBLISHED'}
    pending=set(slugs)-done
    running={}
    with ThreadPoolExecutor(max_workers=4) as pool:
        while pending or running:
            finished=[f for f in running if f.done()]
            for f in finished:
                kind,slug=running.pop(f)
                f.result()
                if kind=='proof':
                    done.add(slug)
                else:
                    stated.add(slug)
            available=4-len(running)
            active={slug for kind,slug in running.values()}
            ready=[s for s in slugs if s in pending and s in stated and s not in active and deps[s]<=done]
            for slug in ready[:available]:
                pending.remove(slug)
                running[pool.submit(worker,slug,specs[slug])]=('proof',slug)
                print('REMOTE DISPATCH',slug,flush=True)
            available=4-len(running)
            active={slug for kind,slug in running.values()}
            unstated=[s for s in slugs if s not in stated and s not in active]
            unstated.sort(key=lambda s: (not deps[s]<=done,slugs.index(s)))
            for slug in unstated[:available]:
                running[pool.submit(statement_worker,slug,specs[slug])]=('statement',slug)
                print('REMOTE PREPARE STATEMENT',slug,flush=True)
            (HERE/'verification'/'milestones-progress.json').write_text(json.dumps({
                'stage':'REMOTE_TOPOLOGICAL_VERIFICATION','local_lean_enabled':False,
                'accepted_supports':len(done),'total_supports':len(slugs),
                'running':[{'kind':kind,'slug':slug} for kind,slug in running.values()],
                'published_statements':len(stated),'pending':len(pending)},indent=2)+'\n',encoding='utf-8')
            if pending and not running:
                raise RuntimeError('No ready support: '+str(sorted(pending)))
            time.sleep(3)
    q.THREAD.allowed={'proof:'+SPECS['certificate']['theorem_name']}
    spec=SPECS['certificate']
    result=publish.submit(spec['theorem_id'],HERE/'platform'/spec['file'],spec['explanation']+
        ' All support targets are Proved. After the user reported a local resource incident, '
        'the complete certificate was verified by the platform in small pieces, with no further local Lean process.',
        q.token(),q.read(),spec['theorem_name'])
    if result['status']!='ACCEPTED':
        raise RuntimeError('The original finite milestone is not ACCEPTED')
    remote.finalize()

if __name__=='__main__':
    while True:
        try:
            main()
            break
        except RuntimeError as error:
            if 'timed out' not in str(error):
                raise
            manifest_path=HERE/'platform'/'milestone35-manifest.json'
            before=manifest_path.read_bytes()
            import refine_remote_groups
            refine_remote_groups.main()
            if manifest_path.read_bytes()==before:
                (HERE/'verification'/'milestones-progress.json').write_text(json.dumps({
                    'stage':'REMOTE_TIMEOUT_REQUIRES_REVIEW','local_lean_enabled':False,
                    'error':str(error)},indent=2)+'\n',encoding='utf-8')
                raise
            import audit_remote_sources
            audit_remote_sources.main()
            print('REMOTE RESUME AFTER FINER SPLIT; no local Lean',flush=True)
