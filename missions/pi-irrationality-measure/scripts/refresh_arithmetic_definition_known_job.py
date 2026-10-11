"""Read-only refresh of the already recorded Arithmetic Definition job."""
import importlib.util
import json
from datetime import datetime, timezone
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
OLD = TASK / "verification/providers-complete-preview/all-shared-safe-leaves/validation/Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic/publication.json"
OUT = TASK / "verification/ap7/arithmetic-definition-known-job-readback.json"
old = json.loads(OLD.read_bytes())
assert old["job_id"] == "3e11cf71-aac6-4b1a-9f1f-389160f4ad75"
assert old["definition_id"] == "6b1ef300-c311-4ddb-b85c-8d588035e79f"
spec = importlib.util.spec_from_file_location("arithmetic_readonly_p2m", ROOT / "scripts/p2m_api.py")
api = importlib.util.module_from_spec(spec)
spec.loader.exec_module(api)
token = api.get_token()
records = []
for route in ("/publish-jobs/" + old["job_id"], "/theorems/" + old["definition_id"]):
    status, body = api._request("GET", route, token=token)
    records.append({"route": route, "http_status": status, "body": json.loads(body)})
report = {"read_only": True, "POST_used": False, "at_utc": datetime.now(timezone.utc).isoformat(),
          "original_publication": OLD.relative_to(TASK).as_posix(), "records": records}
OUT.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"read_only": True, "output": OUT.relative_to(TASK).as_posix(),
                 "statuses": [{"http_status": x["http_status"], "status": x["body"].get("status")}
                              for x in records]}))
