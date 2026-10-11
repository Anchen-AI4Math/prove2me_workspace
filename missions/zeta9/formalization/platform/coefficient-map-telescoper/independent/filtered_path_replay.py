from run_step import *
verify()
old=load(OUT/'historical-cache-resolution.json')
for short,cache in [('rn2',N),('rs2',P)]:
 run('filtered own cache '+short+' actual resolver',OUT/(short+'.lean'),cache,args=[])
run('filtered independent Stage1 graph',OUT/'g.lean',N)
for context,cache in [('native',N),('staged',P)]:
 run('filtered '+context+' Aggregate full kernel equality replay',OUT/('agg-'+context+'-values.lean'),cache)
receipt=load(OUT/'review-compile-receipt.json')
def result(logical):return rows(OUT/next(r for r in receipt['rows'] if r['logical_step']==logical)['log'])
actual=[]
root_cache=(ROOT/'.lake/build/lib/lean').resolve()
for short,cache in [('rn2',N),('rs2',P)]:
 records=result('filtered own cache '+short+' actual resolver')
 parts=[Path(p).resolve() for p in records[0]['LEAN_PATH'].split(';') if p]
 assert parts[0]==cache.resolve() and root_cache not in parts
 for d in records[1:]:
  expected=(cache/(d['module'].replace('.','/')+'.olean')).resolve();assert Path(d['resolved_olean']).resolve()==expected
  previous=next(r for r in old['actual_resolution_records'] if r['module']==d['module'])
  assert sha(expected)==previous['sha256'] and expected.stat().st_size==previous['bytes']
  actual.append(previous)
current=load(OUT/'lean-path-selected.json')['LEAN_PATH'];assert root_cache not in [Path(p).resolve() for p in current.split(';') if p]
assert sorted(rows(OUT/'decl_graph.jsonl'),key=lambda r:r['name'])==sorted(rows(OUT/'retained-final-gate-root-path-visibility/decl_graph.jsonl'),key=lambda r:r['name'])
for context in ['native','staged']:
 oldrows=result('fresh '+context+' Aggregate kernel full values six plus nine rfl')
 newrows=result('filtered '+context+' Aggregate full kernel equality replay')
 assert oldrows==newrows and len(newrows)==15
dump(OUT/'filtered-path-replay.json',{'status':'PASS','actual_filtered_Lean_successes':5,'actual_module_resolutions':actual,'all30_resolutions_exact_same_own_objects':True,'root_proof_fallback_removed':True,'fresh_graph319_exact':True,'native6_and_staged6_full_kernel_equalities_plus18_rfl_replayed':True,'old_successes_guarded_and_not_relabelled':True})
print('Filtered Native13/Platform17 resolution, graph319 and both true kernel/full-value environments all actual0',flush=True)
