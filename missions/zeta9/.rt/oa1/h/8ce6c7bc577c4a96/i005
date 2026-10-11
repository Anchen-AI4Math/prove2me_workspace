"""Source derivative of frozen leaf: explicit actual execution cwd, fixed packages."""
from pathlib import Path
import json, os, subprocess, sys
PROJECT=Path('D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/oa1')
ROOT=Path('D:/users/self_projects/prove2me_workspace')
assert Path.cwd().resolve()==PROJECT.resolve()
environment=dict(os.environ);selected={}
for key in ['LEAN_PATH','LEAN_SRC_PATH']:
    original=[raw for raw in environment.get(key,'').split(os.pathsep) if raw]
    allowed=[]
    for raw in original:
        path=Path(raw)
        absolute=path.resolve() if path.is_absolute() else (PROJECT/path).resolve()
        if absolute.is_relative_to(PROJECT.resolve()) or absolute.is_relative_to((ROOT/'.lake/packages').resolve()):
            allowed.append(str(absolute))
    own=str(PROJECT/'b/lib/lean') if key=='LEAN_PATH' else str(PROJECT)
    if own not in allowed:allowed.insert(0,own)
    environment[key]=os.pathsep.join(allowed)
    selected[key]=dict(original=original,filtered=allowed,actual_execution_cwd=str(PROJECT))
Path(environment['JETS_RUN_PATHS_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\n',encoding='utf-8')
result=subprocess.run(sys.argv[1:],env=environment)
sys.exit(result.returncode)
