from run import *

for name in ['types','values','boundaries','resolver']:
    code=run('actual own '+name,OUT/(name+'.lean'))
    if code:
        sys.exit(code)
print('Own actual full-type/full-value/boundary/resolver sequence completed.',flush=True)
