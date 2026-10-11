"""Read-only audit of the accepted row-sum proof's mission membership and credit."""
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
mission = "d7ce6393-5f06-4635-baa4-569d057ba37c"
theorem = "84aa3fa2-09a3-4b89-af10-e9e55edca8af"
requests = [
    ("me", "/me"),
    ("mission", f"/missions/{mission}"),
    ("leaderboard", f"/missions/{mission}/leaderboard?metric=accepted_solutions&window=all&page=0"),
    ("row_sum_missions", f"/theorems/{theorem}/missions"),
    ("row_sum_submissions", f"/theorems/{theorem}/submissions"),
    ("root_graph", "/theorems/406736ed-98ce-4177-b97f-24de96ba4188/graph"),
]

def fetch(item):
    name, path = item
    status, body = p2m._request("GET", path, token=token)
    try:
        data = json.loads(body)
    except ValueError:
        data = {"non_json_response": body[:500]}
    if name == "me" and status == 200:
        profile = data.get("user", data)
        data = {key: profile.get(key) for key in
                ("id", "user_id", "username", "name", "display_name", "initials") if key in profile}
    return name, {"http_status": status, "path": path, "data": data}

with ThreadPoolExecutor(max_workers=3) as pool:
    results = dict(pool.map(fetch, requests))
report = {"at_utc": datetime.now(timezone.utc).isoformat(), "requests": results}
(DEST / "mission-credit-audit.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
for name, result in results.items():
    data = result["data"]
    if name == "root_graph" and isinstance(data, dict):
        nodes = data.get("nodes", [])
        if isinstance(nodes, list):
            data = {"keys": list(data), "node_count": len(nodes),
                    "row_sum_present": any(theorem in json.dumps(node) for node in nodes)}
    print(json.dumps({"name": name, "http_status": result["http_status"], "data": data}, ensure_ascii=False))
