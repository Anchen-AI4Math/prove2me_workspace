"""Record the human's explicit workflow override without claiming local gates."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
VER=Path(__file__).resolve().parent/'verification'
path=VER/'machine-platform-manifest.json'
receipt={'recorded_at_utc':datetime.now(timezone.utc).isoformat(),
         'user_instruction':'你直接交给prove2me平台验证呗，本地阅读后觉得正确，交给平台来编译，不用本地反复编译检查',
         'user_authorized_server_compilation':True,'validation_mode':'server-first',
         'manifest_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
         'local_full_staged_build_passed':False,'local_full_type_gate_passed':False,
         'native_complete_proof_and_bigospeedrun_previously_verified':True}
(VER/'machine-server-first-authorization.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('Recorded server-first authorization; no local gate marked passed.')
