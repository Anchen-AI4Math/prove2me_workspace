from pathlib import Path
import json,os,subprocess,sys
PROJECT=Path(__file__).resolve().parent
ROOT=Path(r"D:\users\self_projects\prove2me_workspace")
names=[r['name']for r in json.loads((PROJECT/'lake-manifest.json').read_text(encoding='utf8'))['packages']]
environment=dict(os.environ);selected={}
for key in ['LEAN_PATH','LEAN_SRC_PATH']:
    original=[raw for raw in environment.get(key,'').split(os.pathsep)if raw]
    own=PROJECT/'b/lib/lean'if key=='LEAN_PATH'else PROJECT
    packages=[ROOT/'.lake/packages'/n/('.lake/build/lib/lean'if key=='LEAN_PATH'else '')for n in names]
    exact=[own.resolve()]+[q.resolve()for q in packages if q.is_dir()]
    allowed_set={str(q).casefold()for q in exact}
    filtered=[raw for raw in original if str(Path(raw).resolve()).casefold()in allowed_set]
    if str(own.resolve()).casefold()not in{str(Path(raw).resolve()).casefold()for raw in filtered}:filtered.append(str(own))
    environment[key]=os.pathsep.join(filtered)
    selected[key]=dict(original=original,filtered=filtered,allowed_exact_set=[str(q)for q in exact])
Path(environment['MATRIX_RUN_PATHS_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\n',encoding='utf8')
result=subprocess.run(sys.argv[1:],env=environment)
sys.exit(result.returncode)
