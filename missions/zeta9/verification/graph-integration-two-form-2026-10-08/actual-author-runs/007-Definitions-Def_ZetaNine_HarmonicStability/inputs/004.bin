from pathlib import Path
import hashlib,json,os,subprocess,sys,time
sys.dont_write_bytecode=True
TASK=Path(__file__).resolve().parents[2]
WORKSPACE=TASK.parents[1]
OUT=Path(__file__).resolve().parent
PROJECT=TASK/'.rt/gtfa1008'
PYTHON='C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe'
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def binding(p):
 data=p.read_bytes()
 base=TASK if p.is_relative_to(TASK) else WORKSPACE
 return {'task_relative' if base==TASK else 'root_relative':p.relative_to(base).as_posix(),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
def path_of(b):return (TASK if 'task_relative' in b else WORKSPACE)/b.get('task_relative',b.get('root_relative'))
def gate():
 policy=load(OUT/'author-private-inputs-v1.json')
 grant=load(path_of(policy['Root_grant']))
 assert grant['Root_explicit_grant'] and grant['owner']=='two_form_graph_bridge_1008' and grant['lane']==1
 assert binding(path_of(policy['Root_grant']))==policy['Root_grant']
 for row in policy['source_files']:
  assert binding(path_of(row['candidate']))==row['candidate']
  assert binding(path_of(row['private_copy']))==row['private_copy']
 for row in policy['configs']:assert binding(path_of(row))==row
 assert (PROJECT/'.lake/packages').resolve()==(WORKSPACE/'.lake/packages').resolve()
 return policy
def run(module):
 policy=gate();receipt_path=OUT/'author-compile-receipt.json'
 receipt=load(receipt_path) if receipt_path.exists() else {'role':'two-form graph sketch AUTHOR','lane':1,'imported_catalogues_are_explicit_assumptions':True,'api_calls':0,'credential_reads':0,'rows':[]}
 index=len(receipt['rows'])+1;folder=OUT/'actual-author-runs'/(str(index).zfill(3)+'-'+(module or 'runtime').replace('.','-'));folder.mkdir(parents=True)
 inputs=policy['configs']+[binding(Path(__file__)),binding(OUT/'author-private-inputs-v1.json'),policy['Root_grant']]
 args=['--version'];output=None
 if module:
  source=PROJECT/'src'/(module.replace('.','/')+'.lean');assert source.exists();inputs.append(binding(source))
  inputs += [binding(p) for p in sorted((PROJECT/'b/lib/lean').rglob('*')) if p.is_file()]
  output=PROJECT/'b/lib/lean'/(module.replace('.','/')+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
  assert not output.exists(),('new call must not reuse its own prior output',output)
  args=['-o',str(output),str(source)]
 retained=[]
 for i,row in enumerate(inputs):
  snapshot=folder/'inputs'/(str(i).zfill(3)+'.bin');snapshot.parent.mkdir(exist_ok=True);snapshot.write_bytes(path_of(row).read_bytes());retained.append({'original':row,'snapshot':binding(snapshot)})
 env=dict(os.environ)
 for key in ['LEAN_PATH','LEAN_SRC_PATH']:env.pop(key,None)
 env.update(LEAN_NUM_THREADS='1',LAKE_JOBS='1',GRAPH_PATH_RECEIPT=str(folder/'selected-paths.json'))
 command=['lake','env',PYTHON,str(PROJECT/'leaf.py'),'lean','-j1','--root='+str(PROJECT/'src')]+args
 print(str(index)+' '+str(module)+': starting -j1',flush=True);start=time.monotonic()
 result=subprocess.run(command,cwd=PROJECT,env=env,capture_output=True)
 for name,data in [('stdout.log',result.stdout),('stderr.log',result.stderr),('combined.log',result.stdout+result.stderr),('exit.txt',(str(result.returncode)+'\n').encode())]:(folder/name).write_bytes(data)
 outputs=[]
 if output and output.exists():
  snapshot=folder/'outputs/000.bin';snapshot.parent.mkdir();snapshot.write_bytes(output.read_bytes());outputs.append({'original':binding(output),'snapshot':binding(snapshot)})
 row={'index':index,'module':module,'command':command,'cwd':str(PROJECT),'elapsed_seconds':round(time.monotonic()-start,3),'exit_code':result.returncode,'input_bindings':inputs,'retained_inputs':retained,'outputs':outputs,'stdout':binding(folder/'stdout.log'),'stderr':binding(folder/'stderr.log'),'combined':binding(folder/'combined.log'),'exit_file':binding(folder/'exit.txt'),'selected_paths':binding(folder/'selected-paths.json'),'failed_attempt_retained':bool(result.returncode)}
 receipt['rows'].append(row);receipt_path.write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
 print(str(index)+' '+str(module)+': actual exit '+str(result.returncode),flush=True)
 if result.returncode:print((result.stdout+result.stderr).decode('utf-8',errors='replace'),flush=True)
 for key in ['LEAN_PATH','LEAN_SRC_PATH']:
  for raw in load(folder/'selected-paths.json')[key]['filtered']:
   q=Path(raw).resolve();assert q.is_relative_to(PROJECT.resolve()) or q.is_relative_to((WORKSPACE/'.lake/packages').resolve())
 gate();return result.returncode
if __name__=='__main__':
 sys.stdout.reconfigure(encoding='utf-8')
 if sys.argv[1:]==['--all']:
  assert not (OUT/'author-compile-receipt.json').exists()
  if run(None):sys.exit(1)
  for module in gate()['source_compile_order']:
   if run(module):sys.exit(1)
 elif len(sys.argv)==3 and sys.argv[1]=='--module':sys.exit(run(sys.argv[2]))
 else:raise SystemExit('use --all or --module MODULE')
