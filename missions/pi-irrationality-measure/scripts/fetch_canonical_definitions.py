"""Save exact existing platform definition text for reuse auditing; GET requests only."""
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from urllib.parse import quote

sys.stdout.reconfigure(encoding="utf-8")
TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "platform/canonical-definitions"
DEST.mkdir(exist_ok=True)
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
NAMES = ["OAI_PiExponent_FixedDeterminantFamily", "OAI_PiExponent_FormalInterpolationPackets",
         "OAI_PiExponent_AnalyticRemainder"]
spec = importlib.util.spec_from_file_location("p2m", ROOT / "scripts/p2m_api.py")
p2m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p2m)
records = []

def get(path):
    status, body = p2m._request("GET", path, token=p2m.get_token())
    if status != 200:
        raise RuntimeError(f"GET {path}: HTTP {status}")
    return json.loads(body)

for name in NAMES:
    matches, offset = [], 0
    while True:
        body = get("/theorems?theorem_name=" + quote(name) + f"&env={ENV}&limit=100&offset={offset}")
        page = body["theorems"]
        matches.extend(item for item in page if item["theorem_name"] == name)
        offset += len(page)
        if offset >= body["total"]:
            break
        if not page:
            raise RuntimeError("Definition lookup pagination incomplete")
    if len(matches) != 1:
        raise RuntimeError(f"Exact canonical definition identity is not unique: {name}")
    data = get("/theorems/" + matches[0]["theorem_id"])
    if (data.get("theorem_name") != name or data.get("status") != "Definition"
            or data.get("mathlib_rev") != ENV or data.get("visibility") != "public"
            or not isinstance(data.get("definition"), str)):
        raise RuntimeError("Canonical identity/environment/visibility/body differs")
    response = (json.dumps(data, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    (DEST / (name + ".json")).write_bytes(response)
    source = data["definition"].encode("utf-8")
    (DEST / ("Def_" + name + ".lean")).write_bytes(source)
    record = {"name": name, "theorem_id": data["theorem_id"], "env": ENV,
              "visibility": data["visibility"], "status": data["status"],
              "at_utc": datetime.now(timezone.utc).isoformat(),
              "response_sha256": hashlib.sha256(response).hexdigest(),
              "source_sha256": hashlib.sha256(source).hexdigest(), "source_bytes": len(source),
              "validated_reuse": False,
              "pending": ["authoritative AST imports/declarations", "kernel type/value comparison",
                          "scope comparison", "consumer type comparison"]}
    records.append(record)
    print(json.dumps(record))
(DEST / "manifest.json").write_bytes((json.dumps(records, indent=2) + "\n").encode("utf-8"))
