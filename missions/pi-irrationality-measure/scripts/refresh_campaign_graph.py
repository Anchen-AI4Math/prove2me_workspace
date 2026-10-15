"""Read current campaign roots and their actual graphs without changing the platform."""
from __future__ import annotations

import hashlib
import importlib.util
import json
from datetime import datetime, timezone
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification" / ("graph-refresh-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ"))
ROOTS = ["406736ed-98ce-4177-b97f-24de96ba4188", "e717eef2-11b1-4b14-9789-65f52c0502e1"]
spec = importlib.util.spec_from_file_location("pi_graph_api", ROOT / "scripts/p2m_api.py")
api = importlib.util.module_from_spec(spec)
spec.loader.exec_module(api)
token = api.get_token()
DEST.mkdir(parents=True, exist_ok=False)
records = []


def get(path, filename):
    status, raw = api._request("GET", path, token=token)
    body = json.loads(raw)
    if status != 200:
        raise ValueError(f"Graph refresh failed: {path}, HTTP {status}")
    data = (json.dumps(body, ensure_ascii=False, indent=2) + "\n").encode()
    (DEST / filename).write_bytes(data)
    records.append({"path": path, "http_status": status, "file": filename,
                    "sha256": hashlib.sha256(data).hexdigest(),
                    "checked_at_utc": datetime.now(timezone.utc).isoformat()})
    return body


summaries = []
for identifier in ROOTS:
    target = get("/theorems/" + identifier, identifier + "-target.json")
    graph = get("/theorems/" + identifier + "/graph", identifier + "-graph.json")
    decompositions = get("/theorems/" + identifier + "/decompositions", identifier + "-decompositions.json")
    summaries.append({"root_id": identifier, "status": target.get("status"),
                      "nodes": len(graph.get("nodes", [])), "edges": len(graph.get("edges", [])),
                      "graph_fields": list(graph)})
get("/theorems/1a21b159-35ef-490d-8259-021afd876d54", "existing-collision-rate-target.json")
get("/campaigns/pi-irrationality-measure", "campaign.json")

# Only this campaign's proposals are saved, to avoid collecting unrelated work.
proposals = []
offset = 0
while True:
    status, raw = api._request("GET", f"/mission-proposals?limit=100&offset={offset}", token=token)
    if status != 200:
        raise ValueError(f"Proposal refresh failed: HTTP {status}")
    body = json.loads(raw)
    page = body.get("proposals", [])
    proposals.extend(p for p in page if p.get("campaign_id") == "19dd5584-143e-4f30-9851-fb1dcdf9dd7d")
    total = body.get("pagination", {}).get("total", body.get("total"))
    offset += len(page)
    if total is not None and offset >= total:
        break
    if not page or (total is None and len(page) < 100):
        break
    if offset > 10000:
        raise ValueError("Unexpected proposal pagination")
(DEST / "campaign-proposals.json").write_text(json.dumps({"proposals": proposals,
    "account_proposals_scanned": offset, "read_only": True}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
report = {"read_only": True, "updated_at_utc": datetime.now(timezone.utc).isoformat(),
          "roots": summaries, "records": records, "campaign_proposals": [
              {"id": p["id"], "status": p.get("status"), "name": p.get("name")} for p in proposals]}
(DEST / "refresh-report.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"destination": str(DEST), "roots": summaries,
                  "campaign_proposals": report["campaign_proposals"]}, ensure_ascii=False))
