"""Give parsed context commands distinct priority, without changing term ranges."""
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
VER=HERE/'verification'
contexts=json.loads((VER/'machine-scope-contexts.json').read_text(encoding='utf-8'))
items=[]
for module in contexts:
    commands=[c for c in module['commands'] if c['syntaxKind']=='Lean.Parser.Command.mixfix']
    if not commands:continue
    path=HERE/'machine/lean'/Path(*module['module'].split('.')).with_suffix('.lean')
    data=path.read_text(encoding='utf-8').encode()
    for c in commands:
        a,b=c['startOffset'],c['endOffset']
        items.append({'module':module['module'],'offset':a,'source_sha256':hashlib.sha256(data).hexdigest(),
                      'command':data[a:b].decode()})
(VER/'machine-mixfix-priority-inputs.json').write_text(json.dumps(items,ensure_ascii=True)+'\n',encoding='utf-8')
print('Prepared parsed priority slots for',len(items),'mixfix commands')
