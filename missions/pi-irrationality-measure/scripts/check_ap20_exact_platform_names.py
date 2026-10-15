"""Read the exact AP20 analytic and collision names from the official platform.

This runner issues GET requests only. Root controls its execution and credentials.
Every list page and exact-ID readback is saved with its original UTF-8 body.
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
OUTPUT = TASK / "verification/ap20/exact-new-analytic-and-collision-name-lookup.json"
API = ROOT / "scripts/p2m_api.py"
NAMES = ['OAI.PiExponent.LiteralAnalytic.actual_minor_analytic_bound', 'OAI.PiExponent.LiteralAnalytic.actual_minor_expansion', 'OAI.PiExponent.LiteralAnalytic.actualRowCount_pos', 'OAI.PiExponent.LiteralAnalytic.card_choiceFamily_le', 'OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg', 'OAI.PiExponent.LiteralAnalytic.low_transverse_capacity', 'OAI.PiExponent.LiteralAnalytic.lowIndexCount_pos', 'OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le', 'OAI.PiExponent.LiteralAnalytic.norm_choiceMatrix_le', 'OAI.PiExponent.LiteralAnalytic.norm_scalar_product_le', 'OAI.PiExponent.LiteralAnalytic.rowWeight_le_indexWeight_of_ne_zero', 'OAI.PiExponent.LiteralAnalytic.sum_rowWeight_eq', 'OAI.PiExponent.tendsto_collisionRemainder_of_normalized_pow']
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(",", ":")) + "\n").encode("utf-8")


def run():
    need(not OUTPUT.exists(), "Exact-name lookup already exists; refusing overwrite")
    spec = importlib.util.spec_from_file_location("p2m_ap19_analytic_children_lookup", API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = api.get_token()

    def get(route):
        status, raw = api._request("GET", route, token=token)
        try:
            body = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise ValueError("Exact-name GET returned non-JSON") from exc
        return status, raw, body

    records = []
    for name in NAMES:
        pages, matches, offset, total = [], [], 0, None
        while True:
            route = ("/theorems?theorem_name=" + quote(name, safe="") +
                     "&env=" + quote(ENV, safe="") + "&limit=100&offset=" + str(offset))
            status, raw, body = get(route)
            need(status == 200 and isinstance(body, dict)
                 and isinstance(body.get("theorems"), list)
                 and type(body.get("total")) is int and body["total"] >= 0,
                 "Exact-name list status/schema differs")
            if total is None:
                total = body["total"]
            need(body["total"] == total, "Exact-name pagination total changed")
            page = body["theorems"]
            pages.append({"route": route, "http_status": status,
                          "raw_body_utf8": raw,
                          "raw_body_sha256": digest(raw.encode("utf-8")),
                          "parsed_body": body})
            matches.extend(row for row in page if row.get("theorem_name") == name
                           and row.get("mathlib_rev") == ENV)
            offset += len(page)
            if offset >= total:
                break
            need(bool(page), "Exact-name pagination stopped before advertised total")
        need(len(matches) <= 1, "Exact theorem name/environment has ambiguous matches")
        readbacks = []
        for match in matches:
            theorem_id = match.get("theorem_id")
            need(isinstance(theorem_id, str) and theorem_id,
                 "Exact match lacks a theorem ID")
            route = "/theorems/" + quote(theorem_id, safe="")
            status, raw, body = get(route)
            need(status == 200 and body.get("theorem_id") == theorem_id
                 and body.get("theorem_name") == name and body.get("mathlib_rev") == ENV,
                 "Exact-ID readback identity/environment differs")
            readbacks.append({"route": route, "http_status": status,
                              "raw_body_utf8": raw,
                              "raw_body_sha256": digest(raw.encode("utf-8")),
                              "parsed_body": body})
        records.append({"theorem_name": name, "environment": ENV,
                        "lookup_total": total, "pages": pages,
                        "matches": matches, "readbacks": readbacks})

    document = {"schema_version": 1,
                "artifact_kind": "ap20-analytic-and-collision-read-only-exact-name-lookup",
                "read_only": True, "request_methods": ["GET"],
                "environment": ENV,
                "checked_at_utc": datetime.now(timezone.utc).isoformat(),
                "records": records, "credentials_or_tokens_recorded": False}
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_bytes(encode(document))
    return {"output": OUTPUT.relative_to(TASK).as_posix(),
            "output_sha256": digest(OUTPUT.read_bytes()),
            "environment": ENV,
            "matches": [{"theorem_name": row["theorem_name"],
                         "count": len(row["matches"]),
                         "pages": len(row["pages"])} for row in records],
            "read_only": True, "credentials_or_tokens_recorded": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", action="store_true", required=True)
    parser.parse_args()
    print(json.dumps(run(), ensure_ascii=False, indent=2))
