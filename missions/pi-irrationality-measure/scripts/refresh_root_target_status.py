"""Authenticated read-only status refresh for the two fixed campaign targets."""
import importlib.util
import argparse
import json
from datetime import datetime, timezone
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", default=None)
args = parser.parse_args()
spec = importlib.util.spec_from_file_location("pi_root_api", ROOT / "scripts/p2m_api.py")
api = importlib.util.module_from_spec(spec)
spec.loader.exec_module(api)
token = api.get_token()
records = []
for identifier in ["e717eef2-11b1-4b14-9789-65f52c0502e1", "406736ed-98ce-4177-b97f-24de96ba4188"]:
    status, raw = api._request("GET", "/theorems/" + identifier, token=token)
    body = json.loads(raw)
    if status != 200 or body.get("theorem_id") != identifier:
        raise ValueError("Target status refresh did not return the exact target")
    records.append({"http_status": status, "body": body})
report = {"checked_at_utc": datetime.now(timezone.utc).isoformat(), "read_only": True,
          "records": records}
destination = (TASK / (args.output or ("verification/root-platform-status-" +
               datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ") + ".json"))).resolve()
if not destination.is_relative_to((TASK / "verification").resolve()) or destination.exists():
    raise ValueError("Refresh output must be a fresh file within mission verification")
destination.write_bytes((json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode())
print(json.dumps({"targets": [{"theorem_id": r["body"]["theorem_id"],
                               "status": r["body"]["status"]} for r in records]}))
