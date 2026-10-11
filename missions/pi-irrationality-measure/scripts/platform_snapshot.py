"""Authenticated read-only campaign snapshot; never prints credentials."""
import importlib.util
import json
from pathlib import Path
import sys

sys.stdout.reconfigure(encoding="utf-8")
TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
spec = importlib.util.spec_from_file_location("p2m", ROOT / "scripts/p2m_api.py")
p2m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p2m)
token = p2m.get_token(force=True)
saved_version = p2m._load().get("version")
print("SERVER_VERSION", saved_version)
DEST = TASK / "platform"
DEST.mkdir(exist_ok=True)
for name, path in [("campaign", "/campaigns/pi-irrationality-measure"),
                   ("environments", "/environments"),
                   ("proposals", "/mission-proposals?limit=100&offset=0"),
                   ("search", "/theorems?q=PiExponent&limit=100")]:
    status, body = p2m._request("GET", path, token=token)
    if status != 200:
        raise RuntimeError(f"{path}: HTTP {status}: {body[:500]}")
    data = json.loads(body)
    (DEST / f"{name}.json").write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    if name == "campaign":
        print(json.dumps({k: v for k, v in data.items() if k != "entries"}, ensure_ascii=False, indent=2))
    elif name == "environments":
        print(json.dumps(data, ensure_ascii=False))
    elif name == "proposals":
        proposals = data.get("proposals", []) if isinstance(data, dict) else data
        print("RELATED_PROPOSALS", json.dumps([p for p in proposals if
              (p.get("campaign") or {}).get("slug") == "pi-irrationality-measure" or
              "irrationality" in p.get("name", "").lower()], ensure_ascii=False))
    else:
        print("SEARCH", json.dumps(data, ensure_ascii=False))
