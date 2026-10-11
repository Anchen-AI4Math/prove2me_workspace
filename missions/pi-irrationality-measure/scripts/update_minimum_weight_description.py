"""Apply and record one presentation-only description correction after Accepted."""
import hashlib
import importlib.util
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
STAGE = TASK / "verification/independent/OAI_PiExponent_exists_minimum_weight"
IDENTIFIER = "30d83fa5-620d-4059-a909-387ac02d2401"
NAME = "OAI.PiExponent.exists_minimum_weight"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
read = lambda p: json.loads(p.read_bytes())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
m, publication = read(STAGE / "manifest.json"), read(STAGE / "publication.json")
assert publication["confirmed_proved"] and publication["theorem_id"] == IDENTIFIER
assert publication["last_verify_verdict"]["status"] == "ACCEPTED"
payload_path = STAGE / "description-v2-patch.json"
payload = read(payload_path)
assert set(payload) == {"natural_language_statement", "reason"}
spec = importlib.util.spec_from_file_location("description_api", ROOT / "scripts/p2m_api.py")
api = importlib.util.module_from_spec(spec)
spec.loader.exec_module(api)
record_path = STAGE / "description-v2-update.json"
record = read(record_path) if record_path.exists() else {
    "theorem_id": IDENTIFIER, "theorem_name": NAME,
    "original_metadata_sha256": sha(STAGE / "metadata.json"),
    "payload_sha256": sha(payload_path), "formal_statement_unchanged": True,
    "proof_source_sha256": m["solution_sha256"]}
assert record["payload_sha256"] == sha(payload_path)
def save():
    record_path.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
def request(method, **kwargs):
    status, raw = api._request(method, "/theorems/" + IDENTIFIER, token=api.get_token(), **kwargs)
    return {"http_status": status, "body": json.loads(raw)}
def exact(response):
    body = response["body"]
    assert response["http_status"] == 200 and body["theorem_id"] == IDENTIFIER
    assert body["theorem_name"] == NAME and body["mathlib_rev"] == ENV
    assert body["status"] == "Proved" and body["visibility"] == "public"
    assert body["preamble"] == m["preamble"] and body["formal_statement"] == m["formal_statement"]
before = request("GET")
exact(before)
record["readback_before"] = before
save()
if before["body"]["natural_language_statement"] != payload["natural_language_statement"]:
    if record.get("patch_intent"):
        raise RuntimeError("Uncertain description PATCH preserved; no repeat request")
    record["patch_intent"] = {"method": "PATCH", "endpoint": "/theorems/" + IDENTIFIER,
                              "payload_sha256": sha(payload_path)}
    save()
    record["patch_response"] = request("PATCH", data=payload)
    save()
    assert record["patch_response"]["http_status"] == 200
after = request("GET")
exact(after)
assert after["body"]["natural_language_statement"] == payload["natural_language_statement"]
record["readback_after"] = after
record["description_exact_readback"] = True
save()
print(json.dumps({"description_exact_readback": True, "theorem_id": IDENTIFIER,
                  "formal_statement_unchanged": True, "proof_source_unchanged": True}))
