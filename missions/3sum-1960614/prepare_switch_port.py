"""Initialize the legacy source interface for the proved quartic switch."""
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
source=HERE/'verification/upstream/Submission/ThreeSum/Switch.lean'
dest=HERE/'machine/lean/Submission/ThreeSum/Switch.lean'
if not dest.exists():
    dest.write_bytes(source.read_bytes().decode('utf-8-sig').replace('\r\n','\n').encode('utf-8'))
(HERE/'verification/switch-port-manifest.json').write_text(json.dumps({
 'upstream_commit':'2b639655e07421b9ac743de9090459bab473a7c0',
 'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'port_path':dest.relative_to(ROOT).as_posix()},indent=2)+'\n',encoding='utf-8')
