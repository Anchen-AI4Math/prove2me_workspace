"""Check the extracted source payload against its archive manifest, without building."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / "source-manifest.json").read_text(encoding="utf-8-sig"))
checked = 0
for row in manifest["files"]:
    p = ROOT / row["path"]
    data = p.read_bytes()
    assert len(data) == row["bytes"], "Size mismatch: " + row["path"]
    assert hashlib.sha256(data).hexdigest() == row["sha256"], "Hash mismatch: " + row["path"]
    checked += 1
print(json.dumps({"status": "PASS", "payload_members_checked": checked,
                  "manifest_self_hash_omitted": True, "network_operations": False}))
