from collections import Counter
from pathlib import Path
from prepare_A_independent import OUT,load,pathof
pre=load(OUT/'A-personal-author-stock-preflight.json')['stock_precompile_bindings']
print('fields',Counter(next(k for k in ['absolute_path','root_relative','task_relative'] if k in r) for r in pre))
print('packages',Counter('packages/' in pathof(r).as_posix() for r in pre))
print('suffix',Counter(pathof(r).suffix for r in pre))
rows=[r for r in pre if 'batteries' in str(pathof(r))]
print('batteries',len(rows),'sample',rows[:3])
rows=[r for r in pre if str(pathof(r)).endswith('Mathlib.olean')]
print('Mathlib root',rows)
print('Root',__import__('prepare_A_independent').ROOT)
