"""Read the exact AP18 translated-summand theorem name in one environment.

This runner performs GET requests only.  It preserves every list page and any
exact theorem readback, including their original UTF-8 response bytes.
"""
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
STAGE = TASK / "verification/ap18/translated-summand-bound-v2"
OUTPUT = STAGE / "exact-name-lookup.json"
API = ROOT / "scripts/p2m_api.py"
NAME = "OAI.PiExponent.DeterminantAnalyticBound.translated_summand_bound"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(",", ":")) + "\n").encode("utf-8")


def run():
    need(not OUTPUT.exists(), "Exact-name lookup already exists; refusing to overwrite it")
    spec = importlib.util.spec_from_file_location("p2m_ap18_translated_lookup", API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = api.get_token()

    def request(path):
        status, raw = api._request("GET", path, token=token)
        try:
            body = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise ValueError("Exact-name GET returned non-JSON") from exc
        return status, raw, body

    pages, matches, offset = [], [], 0
    while True:
        route = ("/theorems?theorem_name=" + quote(NAME) + "&env=" + ENV
                 + "&limit=100&offset=" + str(offset))
        status, raw, body = request(route)
        need(status == 200 and isinstance(body, dict)
             and isinstance(body.get("theorems"), list)
             and type(body.get("total")) is int and body["total"] >= 0,
             "Exact-name list response schema/status differs")
        page = body["theorems"]
        pages.append({"route": route, "http_status": status,
                      "raw_body_utf8": raw,
                      "raw_body_sha256": sha_bytes(raw.encode("utf-8")),
                      "parsed_body": body})
        matches.extend(row for row in page
                       if row.get("theorem_name") == NAME
                       and row.get("mathlib_rev") == ENV)
        offset += len(page)
        if offset >= body["total"]:
            break
        need(bool(page), "Exact-name pagination ended before advertised total")

    need(len(matches) <= 1, "Exact name/environment has ambiguous matches")
    readbacks = []
    for match in matches:
        theorem_id = match.get("theorem_id")
        need(isinstance(theorem_id, str) and theorem_id,
             "Exact-name match lacks a theorem ID")
        route = "/theorems/" + quote(theorem_id, safe="")
        status, raw, body = request(route)
        need(status == 200 and body.get("theorem_id") == theorem_id
             and body.get("theorem_name") == NAME
             and body.get("mathlib_rev") == ENV,
             "Exact theorem readback identity/environment differs")
        readbacks.append({"route": route, "http_status": status,
                          "raw_body_utf8": raw,
                          "raw_body_sha256": sha_bytes(raw.encode("utf-8")),
                          "parsed_body": body})

    doc = {"schema_version": 1,
           "artifact_kind": "ap18-translated-summand-read-only-exact-name-lookup",
           "read_only": True, "environment": ENV,
           "theorem_name": NAME,
           "checked_at_utc": datetime.now(timezone.utc).isoformat(),
           "pages": pages, "matches": matches, "readbacks": readbacks,
           "credentials_or_tokens_recorded": False,
           "request_methods": ["GET"]}
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
