"""Download only public API reference documents at the recorded official tag."""
import hashlib
import json
import urllib.request
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
DEST = TASK / "verification/api-review-20261011-v0.12.4"
COMMIT = "78989800ba0b3149ee34205257025bd0f617e8ef"
BASE = f"https://raw.githubusercontent.com/prove2me/prove2me_workspace/{COMMIT}/"
NAMES = ["SKILL.md", "references/contribute.md", "references/prove.md", "references/discover.md"]
opener = urllib.request.build_opener(urllib.request.ProxyHandler({
    "http": "http://127.0.0.1:65532", "https": "http://127.0.0.1:65532"}))
rows = []
for name in NAMES:
    with opener.open(BASE + name, timeout=20) as response:
        raw = response.read()
    target = DEST / name
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists() and target.read_bytes() != raw:
        raise ValueError("Public reference bytes changed at fixed commit: " + name)
    target.write_bytes(raw)
    rows.append({"name": name, "url": BASE + name, "sha256": hashlib.sha256(raw).hexdigest(),
                 "bytes": len(raw)})
(DEST / "manifest.json").write_text(json.dumps({"official_commit": COMMIT,
    "official_tag": "v0.12.4", "credentials_used": False, "documents": rows}, indent=2) + "\n",
    encoding="utf-8")
print(json.dumps({"documents": len(rows), "official_commit": COMMIT, "credentials_used": False}))
