from run_author import *
import argparse
p=argparse.ArgumentParser();p.add_argument('--parent-lane-authorized',action='store_true',required=True);p.parse_args()
r=load(OUT/'actual-execution-receipt.json')
for source in ['CoefficientMapFormalTransportData','CoefficientMapFormalTransportBounds']:
 rows=[x for x in r['rows'] if x['mode']=='compile' and x['name']==source]
 assert rows[-1]['actual_exit']==0 and rows[-1]['source']['sha256']==sha(TASK/'formalization'/(source+'.lean'))
for mode,name in [('runtime','actual pinned runtime'),('audit','source-full-audit.lean'),('audit','whole-values.lean'),('audit','endpoint-audit.lean'),('resolver','resolver.lean')]:
 result=run(mode,name)
 if result:raise SystemExit(result)
print('All required actual author audits finished',flush=True)
