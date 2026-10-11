from run_step import *
verify()
retained=OUT/'retained-final-gate-root-path-visibility'
retained.mkdir(exist_ok=True)
for name in ['decl_graph.jsonl','lean-path-selected.json','finalize.py','run_step.py','review-compile-receipt.json']:
 dest=retained/name
 if dest.exists():
  if name!='review-compile-receipt.json':assert sha(dest)==sha(OUT/name)
 else:write(dest,(OUT/name).read_bytes())
enroll=load(OUT/'preparation-enrollment.json');plan=load(BATCH/'root-copy-plan.json')
native=['missions.zeta9.formalization.'+n for n in enroll['original_source_hashes']]+['Definitions.Def_ZetaNine_HarmonicStability','NativeTelescoperAuthorControl','NativeTelescoperIndependentControl','NativeValueComparisonDefinition']
platform=[r['root_relative'].removesuffix('.lean').replace('/','.') for r in plan['required_existing_Definitions']]+[r['root_relative_destination'].removesuffix('.lean').replace('/','.') for r in plan['files']]+['StagedValueComparisonDefinition']
for short,mods,cache in [('rn2',native,N),('rs2',platform,P)]:
 quoted=', '.join(json.dumps(m) for m in mods)
 body='import Lean\nopen Lean\ndef main : IO Unit := do\n  let path ← IO.getEnv "LEAN_PATH"\n  IO.println ((Json.mkObj [("kind", Json.str "actual_search_path"), ("LEAN_PATH", Json.str (path.getD ""))]).compress)\n  for m in (['+quoted+'] : List String) do\n    let p ← Lean.findOLean ((m.splitOn ".").foldl Name.str Name.anonymous)\n    IO.println ((Json.mkObj [("kind", Json.str "actual_module_resolution"), ("module", Json.str m), ("resolved_olean", Json.str p.toString)]).compress)\n'
 write(OUT/(short+'.lean'),body)
 run('historical visible fallback actual '+short+' resolver',OUT/(short+'.lean'),cache,args=[])
receipt=load(OUT/'review-compile-receipt.json');observed=[]
for short,mods,cache in [('rn2',native,N),('rs2',platform,P)]:
 r=next(r for r in receipt['rows'] if r['logical_step']=='historical visible fallback actual '+short+' resolver')
 data=rows(OUT/r['log']);assert len(data)==len(mods)+1
 assert data[0]['kind']=='actual_search_path'
 for m,d in zip(mods,data[1:]):
  path=Path(d['resolved_olean']).resolve();expected=(cache/(m.replace('.','/')+'.olean')).resolve()
  assert d['module']==m and path==expected and path.is_file()
  observed.append({'environment':short,'module':m,'actual_resolved_task_relative':path.relative_to(TASK).as_posix(),'bytes':path.stat().st_size,'sha256':sha(path)})
dump(OUT/'historical-cache-resolution.json',{'status':'ACTUAL_RESOLUTION_ALL_OWN_OBJECTS','historical_root_fallback_visible':True,'actual_resolution_records':observed,'fresh_cache_not_reset':True,'same_immutable_source_object_log_chain':True,'claim_limit':'This actual resolver run verifies identical cache precedence and all required module objects. Historical success logs are retained and are not relabelled as filtered runs.'})
print('Actual historical Native13/Platform17 module resolution:30 own objects, zero Root fallback selections',flush=True)
