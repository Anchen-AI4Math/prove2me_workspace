from pathlib import Path
import json, os, subprocess, sys
ROOT = Path(r"D:\users\self_projects\prove2me_workspace")
PROJECT = Path(__file__).resolve().parent
env = os.environ.copy()
selected = {}
for name in ['LEAN_PATH', 'LEAN_SRC_PATH']:
    old = env.get(name, '')
    paths = [x for x in old.split(os.pathsep) if x]
    keep = []
    for raw in paths:
        p = Path(raw).resolve()
        if p.is_relative_to(PROJECT) or p.is_relative_to(ROOT/'.lake/packages'):
            keep.append(raw)
    if name == 'LEAN_PATH':
        own = str(PROJECT/'b/lib/lean')
        if own not in keep: keep.insert(0, own)
    if name == 'LEAN_SRC_PATH':
        if str(PROJECT) not in keep: keep.insert(0, str(PROJECT))
    env[name] = os.pathsep.join(keep)
    selected[name] = {'original': paths, 'filtered': keep}
label = env['CONNECTION_RUN_LABEL']
receipt = Path(env['CONNECTION_RUN_PATHS_RECEIPT'])
receipt.write_text(json.dumps(selected, indent=2)+'\n', encoding='utf-8')
p = subprocess.run(sys.argv[1:], env=env)
sys.exit(p.returncode)
