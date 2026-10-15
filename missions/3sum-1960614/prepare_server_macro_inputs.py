import json
import hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
VER=HERE/'verification'
manifest=json.loads((VER/'machine-platform-manifest.json').read_text(encoding='utf-8'))
files=[r['path'] for r in manifest['definitions']]
files += [r[k+'_path'] for r in manifest['theorems'] for k in ('theorem','solution')]
(VER/'server-macro-inputs.json').write_text(json.dumps(files)+'\n',encoding='utf-8')
(VER/'server-macro-input-hashes.json').write_text(json.dumps({p:hashlib.sha256((HERE.parents[1]/p).read_bytes()).hexdigest() for p in files},indent=2)+'\n',encoding='utf-8')
print('Prepared',len(files),'files for source-only macro translation')
