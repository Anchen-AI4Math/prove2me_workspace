from pathlib import Path
import json, os, subprocess, sys
PROJECT=Path(__file__).resolve().parent
PACKAGES=Path(r"D:\users\self_projects\prove2me_workspace\.lake\packages").resolve()
env=dict(os.environ)
selected={}
for key in ['LEAN_PATH','LEAN_SRC_PATH']:
    original=[raw for raw in env.get(key,'').split(os.pathsep) if raw]
    allowed=[]
    for raw in original:
        resolved=(PROJECT/Path(raw)).resolve()
        if resolved.is_relative_to(PROJECT.resolve()) or resolved.is_relative_to(PACKAGES):
            allowed.append(str(resolved))
    own=str(PROJECT/'b/lib/lean') if key=='LEAN_PATH' else str(PROJECT)
    if own not in allowed:allowed.insert(0,own)
    env[key]=os.pathsep.join(allowed)
    selected[key]=dict(original=original,filtered=allowed)
selected['actual_environment']={key:env.get(key) for key in ['LEAN_NUM_THREADS','LAKE_JOBS']}
Path(env['ACTUAL_PHASE_PATH_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\n',encoding='utf-8')
result=subprocess.run(sys.argv[1:],env=env)
sys.exit(result.returncode)
