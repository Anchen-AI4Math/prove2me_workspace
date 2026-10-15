"""Read exact next determinant-core names before publishing source-faithful nodes."""
import importlib.util
import json
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import quote

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
NAMES = ["OAI.PiExponent.DeterminantContradiction.actualMean_bounds",
    "OAI.PiExponent.DeterminantContradiction.no_fixed_data_of_interpolation_and_analytic_aggregate",
    "OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound_source017"]
spec = importlib.util.spec_from_file_location("pi_core_api", ROOT / "scripts/p2m_api.py")
api = importlib.util.module_from_spec(spec)
spec.loader.exec_module(api)
token = api.get_token()
rows = []
for name in NAMES:
    status, raw = api._request("GET", "/theorems?theorem_name=" + quote(name) +
                             f"&env={ENV}&limit=100&offset=0", token=token)
    if status != 200:
        raise ValueError("Exact determinant core lookup failed")
    body = json.loads(raw)
    if body.get("total", 0) > 100:
        raise ValueError("Unexpectedly broad exact name lookup")
    matches = [row for row in body.get("theorems", []) if row.get("theorem_name") == name]
    details = []
    for row in matches:
        item_status, item_raw = api._request("GET", "/theorems/" + row["theorem_id"], token=token)
        if item_status != 200:
            raise ValueError("Existing source core theorem readback failed")
        details.append(json.loads(item_raw))
    rows.append({"theorem_name": name, "http_status": status, "matches": details})
path = TASK / "verification" / ("determinant-core-exact-name-lookup-" +
        datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ") + ".json")
path.write_text(json.dumps({"read_only": True, "environment": ENV,
    "checked_at_utc": datetime.now(timezone.utc).isoformat(), "records": rows},
    ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"output": str(path), "matches": [{"name": r["theorem_name"],
    "count": len(r["matches"])} for r in rows]}))
