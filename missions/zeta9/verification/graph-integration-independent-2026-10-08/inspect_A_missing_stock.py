from pathlib import Path
import os,json
from prepare_A_independent import load,OUT,pathof,bind,write

pre=load(OUT/'A-personal-author-stock-preflight.json')
base={os.path.normcase(str(pathof(r).resolve())) for r in pre['stock_precompile_bindings']}
missing={}
for f in (OUT/'A-full-records').glob('*/GAIResolver.jsonl'):
    for line in f.read_text(encoding='utf-8').splitlines():
        r=json.loads(line);key=os.path.normcase(str(Path(r['canonical_olean']).resolve()))
        if '.rt' not in r['canonical_olean'] and key not in base:missing[key]=r
print(json.dumps(dict(missing_count=len(missing),missing=list(missing.values()),matching_Cast_preflight=[r for r in pre['stock_precompile_bindings'] if 'Classes/Cast' in str(r) or 'Classes\\Cast' in str(r)]),ensure_ascii=False,indent=2))
write(OUT/'A-stock-precompile-gap-diagnosis.json',dict(status='FIRST67_MATH_CALLS_PASS_BUT_NATIVE_BASELINE_STOCK_NOT_COMPLETE_FOR_PLATFORM_IMPORTS',missing_count=len(missing),missing_actual_imports=list(missing.values()),new_current_post_run_bindings=[bind(Path(r['canonical_olean'])) for r in missing.values()],first67_complete_compiler_PASS_not_final_prepost_stock_PASS=True,no_backdated_precompile_evidence=True,Lean_calls_in_this_diagnosis=0,API_calls=0))
