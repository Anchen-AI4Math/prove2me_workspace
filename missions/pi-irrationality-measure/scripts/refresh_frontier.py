"""Read the bound-two root and current frontier without replacing good snapshots on errors."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import sys

sys.stdout.reconfigure(encoding="utf-8")
TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "platform"
spec = importlib.util.spec_from_file_location("p2m", ROOT / "scripts/p2m_api.py")
p2m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p2m)
token = p2m.get_token()
root_id = "406736ed-98ce-4177-b97f-24de96ba4188"
requests = [
    ("current-bound-two", f"/theorems/{root_id}"),
    ("current-open-leaves", f"/theorems/{root_id}/open-leaves"),
    ("current-det-row-sum", "/theorems/84aa3fa2-09a3-4b89-af10-e9e55edca8af"),
]
def fetch(item):
    name, path = item
    status, body = p2m._request("GET", path, token=token)
    data = json.loads(body) if status == 200 else None
    if data is not None:
        (DEST / f"{name}.json").write_text(
            json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return {"name": name, "path": path, "http_status": status, "data": data}
with ThreadPoolExecutor(max_workers=3) as pool:
    results = list(pool.map(fetch, requests))
record = {"at_utc": datetime.now(timezone.utc).isoformat(),
          "requests": [{k: v for k, v in r.items() if k != "data"} for r in results]}
(DEST / "last-refresh.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
for result in results:
    data = result.pop("data")
    if isinstance(data, dict) and "theorem_id" in data:
        result.update({k: data.get(k) for k in ("theorem_id", "theorem_name", "status")})
    elif data is not None:
        result["data"] = data
    print(json.dumps(result, ensure_ascii=False))
