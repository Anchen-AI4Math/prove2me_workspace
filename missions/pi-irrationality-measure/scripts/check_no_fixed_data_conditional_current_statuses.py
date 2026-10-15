"""Read current NoFixedData/conditional statuses without invoking old publishers."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path


TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
API = ROOT / "scripts/p2m_api.py"
OUTPUT = TASK / "verification/graph-auto-status-20261012/no-fixed-data-conditional-statuses.json"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
HISTORICAL = TASK / "verification/graph-no-fixed-data-route-20261011-v2/publication-v3/post-acceptance-readbacks"
TARGETS = {
    "NoFixedData": {
        "id": "6348c86e-c85a-4559-99e4-7e0ec083208e",
        "name": "OAI.PiExponent.DeterminantContradiction.no_fixed_data_of_interpolation_and_analytic_aggregate",
        "historical": HISTORICAL / "NoFixedData.json"},
    "conditional": {
        "id": "cbe4fb5f-2db8-4484-b209-ecb4e4efea9a",
        "name": "OAI.PiExponent.DeterminantContradiction.piEventualLowerBound_of_interpolation_and_analytic_aggregate",
        "historical": HISTORICAL / "conditional.json"},
}


def need(ok, message):
    if not ok: raise ValueError(message)


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))


def run():
    need(not OUTPUT.exists(), "Fresh graph-status report already exists; refusing overwrite")
    spec = importlib.util.spec_from_file_location("p2m_api_graph_status", API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = api.get_token()
    rows = {}
    for key, target in TARGETS.items():
        old = read(target["historical"])
        need(old.get("theorem_id") == target["id"]
             and old.get("theorem_name") == target["name"]
             and old.get("mathlib_rev") == ENV and old.get("status") == "Open",
             "Historical exact Open identity differs: " + key)
        route = "/theorems/" + target["id"]
        status, raw = api._request("GET", route, token=token)
        try:
            body = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise ValueError("Current theorem GET returned non-JSON: " + key) from exc
        need(status == 200 and isinstance(body, dict)
             and body.get("theorem_id") == target["id"]
             and body.get("theorem_name") == target["name"]
             and body.get("mathlib_rev") == ENV
             and body.get("status") in {"Open", "Proved"}
             and body.get("preamble") == old.get("preamble")
             and body.get("formal_statement") == old.get("formal_statement"),
             "Current theorem identity/wire/status differs: " + key)
        rows[key] = {"route": route, "http_status": status,
            "raw_body_utf8": raw, "raw_body_sha256": sha_bytes(raw.encode("utf-8")),
            "parsed_body": body, "historical_open_readback":
                target["historical"].relative_to(TASK).as_posix(),
            "historical_open_readback_sha256": sha(target["historical"]),
            "current_status": body["status"],
            "automatically_resolved_to_Proved": body["status"] == "Proved",
            "claimed_as_own_ACCEPTED_submission": False}
    doc = {"schema_version": 1,
        "artifact_kind": "no-fixed-data-conditional-current-status-read-only-report",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "environment": ENV, "read_only": True, "request_methods": ["GET"],
        "old_Open_publishers_invoked": False, "own_ACCEPTED_submission_claimed": False,
        "credentials_or_tokens_recorded": False, "targets": rows}
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_bytes(encode(doc))
    return {"output": OUTPUT.relative_to(TASK).as_posix(),
            "output_sha256": sha(OUTPUT),
            "statuses": {key: row["current_status"] for key, row in rows.items()},
            "read_only": True, "old_Open_publishers_invoked": False,
            "own_ACCEPTED_submission_claimed": False,
            "credentials_or_tokens_recorded": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", action="store_true", required=True)
    parser.parse_args()
    print(json.dumps(run(), ensure_ascii=False, indent=2))
