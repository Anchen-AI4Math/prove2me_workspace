"""Read-only exact-name lookup for the single AP16 selected-minor arithmetic lower-bound theorem."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
from urllib.parse import quote


TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
OUTPUT = TASK / "verification/ap16/selected-minor-arithmetic-lower-bound/exact-name-lookup.json"
API = ROOT / "scripts/p2m_api.py"
NAME = "OAI.PiExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def run():
    need(not OUTPUT.exists(), "Exact-name lookup already exists; refusing to overwrite it")
    spec = importlib.util.spec_from_file_location("p2m_api_read_only", API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = api.get_token()
    pages, matches, offset = [], [], 0
    while True:
        route = ("/theorems?theorem_name=" + quote(NAME) + "&env=" + ENV +
                 "&limit=100&offset=" + str(offset))
        status, raw = api._request("GET", route, token=token)
        raw_bytes = raw.encode("utf-8")
        try:
            body = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise ValueError("Exact-name GET returned non-JSON") from exc
        need(status == 200 and isinstance(body, dict)
             and isinstance(body.get("theorems"), list)
             and type(body.get("total")) is int and body["total"] >= 0,
             "Exact-name GET response schema/status differs")
        page = body["theorems"]
        pages.append({"route": route, "http_status": status,
                      "raw_body_utf8": raw, "raw_body_sha256": sha_bytes(raw_bytes),
                      "parsed_body": body})
        matches.extend(row for row in page if row.get("theorem_name") == NAME
                       and row.get("mathlib_rev") == ENV)
        offset += len(page)
        if offset >= body["total"]:
            break
        need(bool(page), "Exact-name pagination stopped before the advertised total")
    doc = {"schema_version": 1,
           "artifact_kind": "ap16-selected-minor-arithmetic-lower-bound-read-only-exact-name-lookup",
           "read_only": True, "environment": ENV,
           "checked_at_utc": datetime.now(timezone.utc).isoformat(),
           "records": [{"theorem_name": NAME, "http_status": 200,
                        "matches": matches, "pages": pages}],
           "credentials_or_tokens_recorded": False,
           "request_methods": ["GET"]}
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_bytes(encode(doc))
    return {"output": OUTPUT.relative_to(TASK).as_posix(),
            "output_sha256": sha_bytes(OUTPUT.read_bytes()),
            "theorem_name": NAME, "environment": ENV,
            "match_count": len(matches), "pages": len(pages),
            "read_only": True, "credentials_or_tokens_recorded": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", action="store_true", required=True)
    parser.parse_args()
    print(json.dumps(run(), ensure_ascii=False, indent=2))
