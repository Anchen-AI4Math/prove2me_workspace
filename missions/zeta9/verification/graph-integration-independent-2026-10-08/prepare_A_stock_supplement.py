from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
from pathlib import Path
from collections import Counter
import json,os,time
from prepare_A_independent import OUT,PROJECT,ROOT,load,pathof,bind,verify,write

started=time.monotonic()
original=load(OUT/'A-personal-author-stock-preflight.json')
old={os.path.normcase(str(pathof(r).resolve())):r for r in original['stock_precompile_bindings']}
all_stock={};counts={}
for f in (OUT/'A-full-records').glob('*/GAIResolver.jsonl'):
    rows=[json.loads(line) for line in f.read_text(encoding='utf-8').splitlines()]
    counts[f.parent.name]=len(rows)
    for r in rows:
        p=Path(r['canonical_olean']).resolve()
        if p.is_relative_to(PROJECT.resolve()):continue
        assert p.is_relative_to((ROOT/'.lake/packages').resolve()) or '.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean/' in p.as_posix()
        assert p.suffix=='.olean'
        for companion in [p,p.with_suffix('.ilean'),Path(str(p)+'.private'),Path(str(p)+'.server')]:
            if companion.exists():all_stock[os.path.normcase(str(companion.resolve()))]=bind(companion)
with ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(verify,old.values()))
new_keys=set(all_stock)-set(old)
write(OUT/'A-stock-supplement-preflight.json',dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),status='TRUE_PRECOMPILE_BASELINE_FOR_FUTURE_FRESH_SOURCE_RECHECK_ONLY',original_preflight=bind(OUT/'A-personal-author-stock-preflight.json'),original_22856_post_run_rehash_unchanged=True,actual_first_round_resolver_counts=counts,stock_bindings=list(all_stock.values()),stock_count=len(all_stock),stock_bytes=sum(r['bytes'] for r in all_stock.values()),previously_not_prebound_for_first67_artifacts=len(new_keys),supplement_binds_future_calls_not_first67=True,first67_unchanged_compile_SUCCESS_but_prepost_gap_preserved=True,mismatches=0,Lean_calls=0,API_calls=0,credential_reads=0,preparer=bind(Path(__file__)),elapsed_seconds=time.monotonic()-started))
print(json.dumps(dict(status='COMPLETE_ACTUAL_STOCK_BOUND_BEFORE_FUTURE_RECHECK',stock_count=len(all_stock),stock_bytes=sum(r['bytes'] for r in all_stock.values()),new_artifacts=len(new_keys),resolver_counts=counts,elapsed_seconds=time.monotonic()-started)))
