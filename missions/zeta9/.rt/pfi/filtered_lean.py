from pathlib import Path
import json,os,subprocess,sys
project=Path(__file__).resolve().parent
allowed=json.loads((project/'allowed-paths.json').read_text(encoding='utf8'))
env=dict(os.environ); selected={}
for key,allow_key in [('LEAN_PATH','olean_paths'),('LEAN_SRC_PATH','source_paths')]:
    raw=[s for s in env.get(key,'').split(os.pathsep) if s]
    allowed_set={str(Path(s).resolve()).casefold() for s in allowed[allow_key]}
    kept=[s for s in raw if str(Path(s).resolve()).casefold() in allowed_set]
    own=allowed[allow_key][0]
    if str(Path(own).resolve()).casefold() not in {str(Path(s).resolve()).casefold() for s in kept}:
        kept.append(own)
    env[key]=os.pathsep.join(kept)
    selected[key]={'original_Lake_paths':raw,'filtered_exact_allowed_paths':kept,'allowed_exact_set':allowed[allow_key]}
Path(env['NUMERATOR_PF_ENV_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\n',encoding='utf8')
result=subprocess.run(sys.argv[1:],env=env)
sys.exit(result.returncode)
