"""Read pinned public documentation without touching workspace skill files."""
import difflib
import hashlib
import json
import os
from pathlib import Path
import urllib.request

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
COMMIT='38e12f9d215cb103a0f9173ec230a614fcd93b61'
DEST=HERE/'verification/platform-docs-0.12.6'
DEST.mkdir(exist_ok=True)
proxy=urllib.request.ProxyHandler({'http':'http://127.0.0.1:65532','https':'http://127.0.0.1:65532'})
opener=urllib.request.build_opener(proxy)
receipt={'commit':COMMIT,'files':{}}
for name in ['SKILL.md','references/contribute.md','references/prove.md','references/upload_full_project.md','references/mission_captain.md','references/missions.md']:
    url=f'https://raw.githubusercontent.com/prove2me/prove2me_workspace/{COMMIT}/{name}'
    with opener.open(url,timeout=45) as response:data=response.read()
    (DEST/name.replace('/','_')).write_bytes(data)
    original=(ROOT/name).read_text(encoding='utf-8').splitlines()
    changes=list(difflib.unified_diff(original,data.decode().splitlines(),fromfile='local/'+name,tofile='official/'+name))
    receipt['files'][name]={'sha256':hashlib.sha256(data).hexdigest(),'diff_lines':len(changes)}
    print(name,'diff lines:',len(changes),flush=True)
    if name in ['references/contribute.md','references/prove.md','references/upload_full_project.md']:
        print('\n'.join(changes).encode('ascii','backslashreplace').decode()[:9000],flush=True)
(DEST/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
