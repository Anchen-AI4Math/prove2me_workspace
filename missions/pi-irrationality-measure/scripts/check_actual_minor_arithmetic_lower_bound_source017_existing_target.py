"""Read back the one existing AP17 source017 target without mutating the API."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path

import stage_actual_minor_arithmetic_lower_bound_source017_route as route


TASK, ROOT, STAGE = route.TASK, route.ROOT, route.STAGE
OUTPUT = STAGE / "fresh-existing-target-readback.json"
API = ROOT / "scripts/p2m_api.py"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def run():
    need(not OUTPUT.exists(), "Fresh AP17 target readback already exists; refusing overwrite")
    spec = importlib.util.spec_from_file_location("p2m_api_ap17_read_only", API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = api.get_token()
    path = "/theorems/" + route.TARGET_ID
    status, raw = api._request("GET", path, token=token)
    try:
        body = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError("AP17 existing-target GET returned non-JSON") from exc
    saved = route.saved_public_target()
    need(status == 200 and isinstance(body, dict)
         and body.get("theorem_id") == route.TARGET_ID
         and body.get("theorem_name") == route.PLATFORM_NAME
         and body.get("mathlib_rev") == ENV
         and body.get("status") == "Open"
         and body.get("preamble") == saved["preamble"]
         and body.get("formal_statement") == saved["formal_statement"]
         and (body["preamble"] + body["formal_statement"]).encode("utf-8") ==
             route.OPEN_WIRE.read_bytes(),
         "AP17 existing target is no longer the reviewed exact Open wire")
    doc = {"schema_version": 1,
           "artifact_kind": "ap17-source017-existing-target-read-only-fresh-readback",
           "read_only": True, "request_methods": ["GET"],
           "checked_at_utc": datetime.now(timezone.utc).isoformat(),
           "environment": ENV, "route": path, "http_status": status,
           "raw_body_utf8": raw,
           "raw_body_sha256": sha_bytes(raw.encode("utf-8")),
           "parsed_body": body,
           "credentials_or_tokens_recorded": False}
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_bytes(encode(doc))
    return {"output": OUTPUT.relative_to(TASK).as_posix(),
            "output_sha256": sha_bytes(OUTPUT.read_bytes()),
            "theorem_id": route.TARGET_ID, "theorem_name": route.PLATFORM_NAME,
            "status": body["status"], "read_only": True,
            "credentials_or_tokens_recorded": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", action="store_true", required=True)
    parser.parse_args()
    print(json.dumps(run(), ensure_ascii=False, indent=2))
