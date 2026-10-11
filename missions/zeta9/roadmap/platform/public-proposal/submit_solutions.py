"""Submit the eight prepared proofs to the public mission once it is live.

The mission only accepts submissions after moderator approval (`mission_id` non-empty and
each item has a `theorem_id`). Until then `--submit` refuses; `--check` works offline.

Modes:
  --check   verify every local solution against its draft statement (no network writes)
  --submit  post each proof to its theorem (idempotent; records submission ids)
  --poll    read back the recorded submission statuses

The compiled theorems exist as soon as the human clicks "Submit Proposal", i.e. while the
proposal is still `In review` and `mission_id` is empty. Submitting at that point is therefore
possible but only on request: pass `--allow-pre-approval` (optionally with `--only Z9N.XXX`).
"""
from __future__ import annotations

import argparse
import hashlib
import re
import json
import sys
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[4]
sys.path.insert(0, str(HERE.parent))
from submit_solved_milestones import post_multipart  # noqa: E402
from build_public_proposal import RECEIPT, SPEC, get_token, request  # noqa: E402

SUBMISSIONS = HERE / "submissions-receipt.json"


def squash(text: str) -> str:
    return " ".join(text.split())


def load() -> dict[str, Any]:
    if SUBMISSIONS.exists():
        return json.loads(SUBMISSIONS.read_text(encoding="utf-8"))
    return {"items": {}}


def save(data: dict[str, Any]) -> None:
    SUBMISSIONS.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n",
                           encoding="utf-8")


def signature(short_name: str, source: str) -> str:
    return squash(source.split(f"theorem {short_name}", 1)[1].split(":= by", 1)[0])


def check() -> None:
    ok = True
    for item in SPEC["draft_items"]:
        short_name = item["theorem_name"].split(".")[-1]
        draft = (HERE / item["code_path"]).read_text(encoding="utf-8")
        solution_path = HERE / "solutions" / f"Sol_Zeta9Note_{short_name}.lean"
        explanation_path = HERE / "solutions" / f"{short_name}-explanation.md"
        problems = []
        if not solution_path.exists():
            problems.append("solution file missing")
        else:
            source = solution_path.read_text(encoding="utf-8")
            if re.search(r"(?m)^\s*sorry\b", source):
                problems.append("solution contains a `sorry` placeholder")
            if source.count("theorem solution") != 1:
                problems.append("solution is not a single root-level `theorem solution`")
            elif signature(short_name, draft) != signature("solution", source):
                problems.append("solution signature differs from the draft statement")
        if not explanation_path.exists():
            problems.append("explanation missing")
        elif len(explanation_path.read_text(encoding="utf-8").strip()) < 200:
            problems.append("explanation too short")
        print(f"[{'OK ' if not problems else 'BAD'}] {item['theorem_name']}"
              + ("" if not problems else " -> " + "; ".join(problems)))
        ok = ok and not problems
    print("check passed" if ok else "check FAILED")
    if not ok:
        raise SystemExit(1)


def submit(allow_pre_approval: bool = False, only: str | None = None) -> None:
    check()
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    if not receipt.get("mission_id") and not allow_pre_approval:
        raise RuntimeError("Mission is not live yet (mission_id is empty). "
                           "Wait for moderator approval, then re-run --status first; "
                           "or pass --allow-pre-approval to post onto the compiled "
                           "theorems while the proposal is still in review.")
    theorem_ids = receipt.get("local_theorem_ids", {})
    missing = [k for k, v in theorem_ids.items() if not v]
    if missing:
        raise RuntimeError(f"No theorem_id for {', '.join(sorted(missing))}; "
                           "run --status to refresh after approval")
    token = get_token()
    data = load()
    for item in SPEC["draft_items"]:
        local_id = item["local_id"]
        if only and local_id != only:
            continue
        short_name = item["theorem_name"].split(".")[-1]
        entry = data["items"].setdefault(local_id, {})
        if entry.get("submission_id"):
            print(f"Already submitted {item['theorem_name']}")
            continue
        theorem_id = theorem_ids[local_id]
        theorem = request("GET", f"/theorems/{theorem_id}", token)
        if theorem.get("visibility") != "public":
            raise RuntimeError(f"Expected a public theorem: {item['theorem_name']}")
        if theorem.get("status") not in ("Open", None):
            print(f"Skipping {item['theorem_name']}: status={theorem.get('status')}")
            continue
        source = (HERE / "solutions" / f"Sol_Zeta9Note_{short_name}.lean").read_text(
            encoding="utf-8")
        if squash(theorem["formal_statement"].split(f"theorem {short_name}", 1)[1]
                  .split(":= by sorry", 1)[0]) != signature("solution", source):
            raise RuntimeError(f"Live theorem differs from the local solution: "
                               f"{item['theorem_name']}")
        explanation = (HERE / "solutions" / f"{short_name}-explanation.md").read_text(
            encoding="utf-8")
        path = HERE / "solutions" / f"Sol_Zeta9Note_{short_name}.lean"
        result = post_multipart(token, theorem_id, path, explanation)
        if not result.get("submission_id"):
            raise RuntimeError(f"No submission id for {item['theorem_name']}: {result}")
        entry["submission_id"] = result["submission_id"]
        entry["status"] = result.get("status")
        entry["theorem_id"] = theorem_id
        entry["solution_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
        save(data)
        print(f"Submitted {item['theorem_name']}: {entry['submission_id']}")
    save(data)
    print(f"{sum(1 for e in data['items'].values() if e.get('submission_id'))}"
          f"/{len(SPEC['draft_items'])} proofs submitted. Run --poll to track them.")


def poll() -> None:
    token = get_token()
    data = load()
    for local_id, entry in data["items"].items():
        if not entry.get("submission_id"):
            continue
        sub = request("GET", f"/submissions/{entry['submission_id']}", token)
        entry["status"] = sub.get("status")
        print(f"{local_id}: {entry.get('status')}")
    save(data)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--submit", action="store_true")
    parser.add_argument("--poll", action="store_true")
    parser.add_argument("--allow-pre-approval", action="store_true")
    parser.add_argument("--only", default=None,
                        help="submit a single local id, e.g. Z9N.CONE")
    args = parser.parse_args()
    if args.submit:
        submit(args.allow_pre_approval, args.only)
    elif args.poll:
        poll()
    elif args.check:
        check()
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
