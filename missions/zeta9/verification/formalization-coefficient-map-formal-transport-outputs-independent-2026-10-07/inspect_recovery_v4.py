from pathlib import Path
import json,sys,concurrent.futures
import inspect_prepare as p
OUT=p.OUT
checks=[]
def ck(label,b):
 checks.append(dict(label=label,passed=bool(b)))
 assert b,label

def main():
 ck('author frozen report exact SHA',p.sha(p.AUTHOR/'author-audit.json')==p.AUTHOR_SHA)
 a=p.load(p.AUTHOR/'author-audit.json')
 ck('author PASS finite scope',a['verdict']=='PASS' and len(a['stable_files'])==636)
 rows=list(a['stable_files'])
 prep=p.load(OUT/'source-preparation.json')
 ck('source-preparation exact SHA',p.sha(OUT/'source-preparation.json')=='57c9cd77fe87436a8563bf191013063f4821537651655fe129a8d3d695dfad56')
 rows+=prep['stable_files']
 r=p.load(OUT/'execution-receipt.json')
 ck('all24 prior actual calls exit0',len(r['rows'])==24 and all(x['exit_code']==0 and x['all_subprocess_handles_terminal'] for x in r['rows']))
 byrel={}
 names=[x['name'] for x in p.load(p.PROJECT/'lake-manifest.json')['packages']]
 for x in r['rows']:
  for key in ['input_bindings','output_bindings','evidence_bindings']:rows+=x[key]
  for pair in x['immutable_input_output_snapshots']:
   rows+=[pair['original'],pair['retained']]
   ck('snapshot pair '+x['label']+' '+pair['retained']['task_relative'],pair['original']['sha256']==pair['retained']['sha256'] and pair['original']['bytes']==pair['retained']['bytes'])
  ck('recorded own project '+x['label'],Path(x['execution_CWD']).resolve()==p.PROJECT.resolve() and '-j1' in x['command'])
  f=p.TASK/x['folder_task_relative']
  ck('actual exit txt '+x['label'],int((f/'exit.txt').read_text())==0)
  paths=p.load(f/'selected-paths.json')
  for k in ['LEAN_PATH','LEAN_SRC_PATH']:
   own=p.PROJECT/('b/lib/lean' if k=='LEAN_PATH' else '')
   package_paths=[p.ROOT/'.lake/packages'/n/('.lake/build/lib/lean' if k=='LEAN_PATH' else '') for n in names]
   expected={str(t.resolve()).casefold() for t in [own]+package_paths if t.is_dir()}
   allowed={str(Path(t).resolve()).casefold() for t in paths[k]['allowed_exact_set']}
   ck('exact expected own-and-fixed-package allowlist '+x['label']+' '+k,allowed==expected)
   ck('filtered path allowlist '+x['label']+' '+k,all(str(Path(t).resolve()).casefold() in expected for t in paths[k]['filtered']))
   ck('no shared Root object search '+x['label']+' '+k,str(p.ROOT.resolve()).casefold() not in allowed and str((p.ROOT/'.lake/build/lib/lean').resolve()).casefold() not in allowed)
  for b in x['output_bindings']:
   ck('prior object SOURCE invocation recorded '+b['task_relative'],b['task_relative'].startswith('.rt/oi7/b/lib/lean/') and any(v.endswith('.lean') for v in x['command']) and '-o' in x['command'])
   byrel[b['task_relative']]=b
 for b in rows:
  rel=b.get('task_relative',b.get('root_relative'))
  ck('relative path safe '+rel,not Path(rel).is_absolute() and '..' not in Path(rel).parts and Path(rel).name not in ['credentials.json','.env'])
 def check_binding(b):
  path=p.resolve(b)
  return str(path),path.stat().st_size==b['bytes'] and p.sha(path)==b['sha256']
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  for path,ok in pool.map(check_binding,rows):ck('exact content binding '+path,ok)
 objects={p.bind(t)['task_relative'] for t in (p.PROJECT/'b/lib/lean').rglob('*.olean')}
 ck('all23 objects have own previous actual0 output bindings',len(objects)==23 and objects==set(byrel))
 ck('21 independent fresh closure source count',len(prep['native_sources'])==21)
 ck('verified Outputs SOURCE true SHA',p.sha(p.PROJECT/'missions/zeta9/formalization/CoefficientMapFormalTransportOutputs.lean')==p.SOURCE_SHA)
 ck('uncompiled shared Outputs not substituted',p.sha(p.TASK/'formalization/CoefficientMapFormalTransportOutputs.lean')==a['original_shared_source']['sha256'] and a['original_shared_source']['sha256']!=p.SOURCE_SHA)
 actualdirs={d.name for d in (OUT/'actual-runs').iterdir() if d.is_dir()}
 ck('no orphan prior actual directories',actualdirs=={Path(x['folder_task_relative']).name for x in r['rows']})
 result=dict(verdict='PASS_PREVIOUS_INDEPENDENT_SOURCE_RUNS_REVALIDATED',author_binding_count=636,previous_independent_actual_calls=24,previous_independent_compiled_objects=23,total_binding_rows_rehashed=len(rows),checks=checks,source_preparation=p.bind(OUT/'source-preparation.json'),previous_execution_receipt=p.bind(OUT/'execution-receipt.json'),objects=[byrel[k] for k in sorted(byrel)],reuse_disclosure='24 actual0 SOURCE compiler runs and 23 proof objects originate from the previous independent reviewer in the same oi7 project; all exact hashes, immutable snapshots, source inputs, terminal exit receipts and restricted paths personally revalidated; no author or Root proof object copied',new_reviewer='outputs_independent_recovery_1007',foreign_proof_objects_borrowed=False,independent_full_outputs_PASS_claimed=False,earlier_pure_inspection_failure='Inline v3 assertion wrongly rejected fixed batteries/Qq/aesop/etc package paths by matching .lake/build/lib/lean substring; no Lean/API invoked; v4 compares independently computed exact package allowlist instead')
 output=OUT/'recovery-inspection-v4.json';assert not output.exists();p.dump(output,result)
 print(json.dumps(dict(verdict=result['verdict'],checks=len(checks),bindings=len(rows),sha256=p.sha(output)),indent=2))
if __name__=='__main__':
 sys.stdout.reconfigure(encoding='utf-8')
 try:main()
 except Exception as e:
  p.dump(OUT/'recovery-inspection-v4-failure.json',dict(error=str(e),checks=checks,Lean_invocations=0));raise
