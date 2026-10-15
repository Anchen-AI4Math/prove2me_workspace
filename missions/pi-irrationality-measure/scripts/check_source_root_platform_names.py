"""Read exact source parent names before creating a source-faithful root reduction."""
import importlib.util
import json
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import quote

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
spec = importlib.util.spec_from_file_location("pi_parent_api", ROOT / "scripts/p2m_api.py")
api = importlib.util.module_from_spec(spec)
spec.loader.exec_module(api)
token = api.get_token()
names = ["OAI.PiExponent.DeterminantContradiction.piEventualLowerBound_of_interpolation_and_analytic_aggregate",
         "OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation", "OAI.PiExponent.LiteralAnalytic.analyticAggregate"]
rows = []
for name in names:
    status, raw = api._request("GET", "/theorems?theorem_name=" + quote(name) + "&limit=100&offset=0", token=token)
    if status != 200:
        raise ValueError("Exact source parent lookup failed")
    body = json.loads(raw)
    matches = [row for row in body.get("theorems", []) if row.get("theorem_name") == name]
    details = []
    for row in matches:
        item_status, item_raw = api._request("GET", "/theorems/" + row["theorem_id"], token=token)
        if item_status != 200:
            raise ValueError("Existing source parent readback failed")
        details.append(json.loads(item_raw))
    rows.append({"theorem_name": name, "http_status": status, "matches": details,
                 "lookup_total": body.get("total")})
path = TASK / "verification" / ("source-root-exact-name-lookup-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ") + ".json")
path.write_text(json.dumps({"read_only": True, "checked_at_utc": datetime.now(timezone.utc).isoformat(),
    "records": rows}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"output": str(path), "matches": [{"name": r["theorem_name"], "count": len(r["matches"])} for r in rows]}))
