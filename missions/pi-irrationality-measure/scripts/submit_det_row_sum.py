"""Submit the locally verified direct row-sum proof once, or poll its recorded submission."""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.stdout.reconfigure(encoding="utf-8")
TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "platform"
record_path = DEST / "det-row-sum-submission.json"
intent_path = DEST / "det-row-sum-submit-intent.json"
source = ROOT / "Solutions/Sol_matrix_det_norm_le_prod_row_sum.lean"
theorem_id = "84aa3fa2-09a3-4b89-af10-e9e55edca8af"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--poll", action="store_true")
args = parser.parse_args()
spec = importlib.util.spec_from_file_location("p2m", ROOT / "scripts/p2m_api.py")
p2m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p2m)
if args.poll:
    record = json.loads(record_path.read_text(encoding="utf-8"))
    submission_id = record["response"].get("submission_id") or record["response"].get("id")
    if not submission_id:
        raise SystemExit("No recorded submission id; inspect the stored response before retrying")
    status, body = p2m._request("GET", f"/verify?submission_id={submission_id}", token=p2m.get_token())
    if status == 200:
        record["last_verdict"] = json.loads(body)
        record["polled_at_utc"] = datetime.now(timezone.utc).isoformat()
        record_path.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(status)
    print(body)
elif intent_path.exists() or record_path.exists():
    raise SystemExit("A submission attempt is already recorded; poll or inspect it rather than posting twice")
else:
    preflight = json.loads((DEST / "det-row-sum-preflight.json").read_text(encoding="utf-8"))
    source_bytes = source.read_bytes()
    sha = hashlib.sha256(source_bytes).hexdigest()
    if not (preflight["source"] == source.relative_to(ROOT).as_posix()
            and preflight["source_sha256"] == sha and preflight["source_unchanged"]
            and preflight["exit_code"] == 0 and not preflight["timed_out"]
            and preflight["timeout_seconds"] <= 300):
        raise SystemExit("The exact submission bytes must have a successful strict preflight")
    expected_axioms = "'solution' depends on axioms: [propext, Classical.choice, Quot.sound]"
    if expected_axioms not in (ROOT / preflight["log"]).read_text(encoding="utf-8"):
        raise SystemExit("Missing clean solution axiom audit")
    explanation = (DEST / "det-row-sum-explanation.md").read_text(encoding="utf-8")
    token = p2m.get_token()
    record = {"theorem_id": theorem_id, "source_sha256": sha, "preflight": preflight,
              "attempt_at_utc": datetime.now(timezone.utc).isoformat()}
    intent_path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    body, ctype = p2m._multipart(
        {"theorem_id": theorem_id, "proof_type": "prove", "explanation": explanation},
        {"file": (source.name, source_bytes)})
    status, response = p2m._request("POST", "/verify", token=token, raw_body=body, ctype=ctype)
    record["http_status"] = status
    record["response"] = json.loads(response)
    record_path.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(status)
    print(response)
