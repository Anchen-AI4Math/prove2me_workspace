from pathlib import Path
import json,os,subprocess,sys
PROJECT=Path(__file__).resolve().parent
PACKAGES=Path(r"D:\users\self_projects\prove2me_workspace\.lake\packages").resolve()
env=dict(os.environ);selected={}
for key in ['LEAN_PATH','LEAN_SRC_PATH']:
    original=[x for x in env.get(key,'').split(os.pathsep) if x]
    allowed=[]
    for raw in original:
        p=(PROJECT/Path(raw)).resolve()
        if p.is_relative_to(PROJECT.resolve()) or p.is_relative_to(PACKAGES):allowed.append(str(p))
    own=str(PROJECT/('b/lib/lean' if key=='LEAN_PATH' else 'src'))
    if own not in allowed:allowed.insert(0,own)
    env[key]=os.pathsep.join(allowed);selected[key]=dict(original=original,filtered=allowed)
selected['actual_environment']={k:env.get(k) for k in ['LEAN_NUM_THREADS','LAKE_JOBS']}
Path(env['GAI_PATH_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\n',encoding='utf-8')
sys.exit(subprocess.run(sys.argv[1:],env=env).returncode)
