from pathlib import Path
import json, os, subprocess, sys
PROJECT=Path(__file__).resolve().parent
ROOT=Path(r'D:\users\self_projects\prove2me_workspace')
env=dict(os.environ); selected={'actual_execution_CWD':str(PROJECT)}
names=[x['name'] for x in json.loads((PROJECT/'lake-manifest.json').read_text(encoding='utf-8'))['packages']]
for key in ['LEAN_PATH','LEAN_SRC_PATH']:
    own=PROJECT/'b/lib/lean' if key=='LEAN_PATH' else PROJECT
    packages=[ROOT/'.lake/packages'/n/('.lake/build/lib/lean' if key=='LEAN_PATH' else '') for n in names]
    exact=[own.resolve()]+[x.resolve() for x in packages if x.is_dir()]
    allowed={str(x).casefold() for x in exact}
    original=[x for x in env.get(key,'').split(os.pathsep) if x]
    filtered=[]
    for raw in original:
        candidate=Path(raw)
        resolved=(candidate if candidate.is_absolute() else PROJECT/candidate).resolve()
        if str(resolved).casefold() in allowed and str(resolved) not in filtered:
            filtered.append(str(resolved))
    own_text=str(own.resolve())
    if own_text not in filtered: filtered.insert(0,own_text)
    env[key]=os.pathsep.join(filtered)
    selected[key]=dict(original=original,filtered=filtered,allowed_exact_set=[str(x) for x in exact])
Path(env['OUTPUTS_PLATFORM_PATH_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\n',encoding='utf-8')
result=subprocess.run(sys.argv[1:],env=env)
sys.exit(result.returncode)
