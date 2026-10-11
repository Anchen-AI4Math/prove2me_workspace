"""Future child-Leaf helper: permit only this project and fixed package paths."""
from pathlib import Path
import json, os, subprocess, sys

PROJECT = Path(__file__).resolve().parent
ROOT = Path(r'D:\users\self_projects\prove2me_workspace')
environment = dict(os.environ)
selected = {}
for key in ['LEAN_PATH', 'LEAN_SRC_PATH']:
    original = [raw for raw in environment.get(key,'').split(os.pathsep) if raw]
    allowed = []
    for raw in original:
        path = Path(raw).resolve()
        if path.is_relative_to(PROJECT.resolve()) or path.is_relative_to((ROOT/'.lake/packages').resolve()):
            allowed.append(str(path))
    own = str(PROJECT/'b/lib/lean') if key == 'LEAN_PATH' else str(PROJECT)
    if own not in allowed: allowed.insert(0,own)
    environment[key] = os.pathsep.join(allowed)
    selected[key] = dict(original=original,filtered=allowed)
Path(environment['NUMERATOR_PF_RUN_PATHS_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\n',encoding='utf-8')
result = subprocess.run(sys.argv[1:],env=environment)
sys.exit(result.returncode)
