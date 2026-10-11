"""Read the current campaign graph and exact open-leaf interfaces; no publication."""
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
frontier = json.loads((DEST / "current-open-leaves.json").read_text(encoding="utf-8"))
requests = [("current-root-graph", "/theorems/406736ed-98ce-4177-b97f-24de96ba4188/graph")]
requests += [("leaf-" + leaf["theorem_id"], "/theorems/" + leaf["theorem_id"])
             for leaf in frontier["open_leaves"]]

def fetch(item):
    name, path = item
    status, body = p2m._request("GET", path, token=token)
    if status != 200:
        return {"name": name, "http_status": status}
    data = json.loads(body)
    (DEST / (name + ".json")).write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n",
                                       encoding="utf-8")
    return {"name": name, "http_status": status,
            **{key: data.get(key) for key in ("theorem_id", "theorem_name", "status")}}

with ThreadPoolExecutor(max_workers=4) as pool:
    results = list(pool.map(fetch, requests))
(DEST / "last-stage-target-refresh.json").write_text(
    json.dumps({"at_utc": datetime.now(timezone.utc).isoformat(), "results": results}, indent=2) + "\n",
    encoding="utf-8")
for result in results:
    print(json.dumps(result))
