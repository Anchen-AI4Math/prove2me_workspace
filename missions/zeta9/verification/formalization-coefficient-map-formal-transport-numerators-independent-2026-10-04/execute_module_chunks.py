"""One granted lane, same full Expr/schema, genuine source module chunks only."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.stdout.reconfigure(encoding='utf8')
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[3]
TASK=OUT.parents[1]
DRIVER=OUT/'run_after_lane_grant_v2.py'
manifest=json.loads((OUT/'module-chunk-manifest.json').read_text(encoding='utf8'))
for i,row in enumerate(manifest['chunks'],1):
    source=TASK/row['task_relative']
    assert source.stat().st_size==row['bytes'] and hashlib.sha256(source.read_bytes()).hexdigest()==row['sha256']
    print('START same-schema source chunk',i,'/17',row['module'],'declarations',row['declaration_count'],flush=True)
    result=subprocess.run([sys.executable,str(DRIVER),'audit','--file',row['file'],
        '--lane-grant','ROOT_EXPLICIT_LANE_GRANT'])
    receipt=json.loads((OUT/'actual-execution-receipt.json').read_text(encoding='utf8'))['rows'][-1]
    text=(ROOT/receipt['log']['root_relative']).read_text(encoding='utf8',errors='replace')
    if result.returncode:
        print('\n'.join(line for line in text.splitlines() if 'error' in line.lower())[:10000],flush=True)
        print('STOP: actual failed chunk retained',row['module'],flush=True)
        raise SystemExit(result.returncode)
    records=[json.loads(line) for line in text.splitlines() if line.startswith('{')]
    assert len(records)==row['declaration_count'] and all(r['kind']=='actual_source_declaration' for r in records)
    print('COMPLETE real source records',len(records),row['module'],flush=True)
print('All seventeen same-schema chunks terminal actual0, full389 real declaration records.',flush=True)
