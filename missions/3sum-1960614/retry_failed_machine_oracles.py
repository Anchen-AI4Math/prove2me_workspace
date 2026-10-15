"""Repair failed completed receipts without interrupting the supervised queue.

Run alongside at most one extraction worker. The caller lowers the shared
resource gate first. Only matching failed receipts are retried; successful
facts are never replaced. Source/oracle hashes are checked before and after.
"""
from datetime import datetime,timezone
import json
import os
from pathlib import Path
import subprocess
from machine_skeleton import HERE,ROOT,VER,sha

OUT=VER/'sketch-oracles'
TOOL=ROOT/'scripts/extract_sketch_info.lean'
LAKE=Path.home()/'.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake.exe'
tool_hash=sha(TOOL.read_bytes())
env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
repaired=[]
for stamp in sorted(OUT.glob('*.receipt.json')):
    old=json.loads(stamp.read_text(encoding='utf-8'))
    if old.get('exit_code')==0:continue
    module=old['module']
    source=HERE/'machine/lean'/Path(*module.split('.')).with_suffix('.lean')
    assert old['source_sha256']==sha(source.read_bytes())
    assert old['oracle_sha256']==tool_hash
    facts=ROOT/old['facts_path'];temp=facts.with_suffix('.retry.jsonl')
    err=facts.with_suffix('.retry.stderr.txt')
    print('Retrying failed completed module:',module,flush=True)
    with temp.open('w',encoding='utf-8') as out,err.open('w',encoding='utf-8') as stderr:
        run=subprocess.run([str(LAKE),'env','lean','--run',str(TOOL),str(source)],
                           cwd=ROOT,env=env,stdout=out,stderr=stderr)
    assert run.returncode==0,('Retry failed; original failed receipt retained',module,run.returncode)
    records=[json.loads(s) for s in temp.read_text(encoding='utf-8').splitlines() if s.strip()]
    assert all(r['kind'] in ['decl','ref'] for r in records)
    assert sha(source.read_bytes())==old['source_sha256'] and sha(TOOL.read_bytes())==tool_hash
    temp.replace(facts)
    receipt={**old,'exit_code':0,'declaration_count':sum(r['kind']=='decl' for r in records),
             'recovered_at_utc':datetime.now(timezone.utc).isoformat(),
             'recovery_stderr_path':err.relative_to(ROOT).as_posix()}
    temporary=stamp.with_suffix('.tmp')
    temporary.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    temporary.replace(stamp)
    repaired.append(module)
    print('Recovered',module,receipt['declaration_count'],'official declaration facts',flush=True)
(VER/'machine-oracle-recovery.json').write_text(json.dumps({'repaired_modules':repaired,
    'oracle_sha256':tool_hash,'checked_at_utc':datetime.now(timezone.utc).isoformat()},indent=2)+'\n',encoding='utf-8')
print('Recovery complete:',len(repaired),'modules.',flush=True)
