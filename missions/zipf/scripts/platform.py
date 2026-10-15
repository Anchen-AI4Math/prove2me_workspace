"""Read, submit, and record only the Zipf mission using the workspace API client."""
import argparse
import concurrent.futures
import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
import p2m_api as api

MISSION = "9d7a43ac-2157-449b-a0b5-93d1d19ef7c2"
MAIN = "3db55d74-324f-4340-aed9-9dbf6411b23f"
EVIDENCE = ROOT / "missions/zipf/verification"
MANIFEST = EVIDENCE / "submissions.json"


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def request(method, path, token, **kwargs):
    status, body = api._request(method, path, token=token, **kwargs)
    if not 200 <= status < 300:
        raise RuntimeError(f"{method} {path}: HTTP {status}: {body[:1000]}")
    return json.loads(body)


def snapshot(path, token, filename):
    data = request("GET", path, token)
    save(EVIDENCE / filename, {
        "path": path, "fetched_at": datetime.now(timezone.utc).isoformat(), "data": data
    })
    return data


def sync(token):
    milestones = snapshot(f"/missions/{MISSION}/milestones?limit=100&offset=0", token,
                          "milestones-current.json")
    theorem_ids = [MAIN] + [m["theorem"]["id"] for m in milestones["milestones"]]
    tasks = []
    for theorem_id in theorem_ids:
        tasks.append((f"/theorems/{theorem_id}", f"current-{theorem_id}.json"))
        for kind in ("submissions", "decompositions", "mentions"):
            tasks.append((f"/theorems/{theorem_id}/{kind}", f"{kind}-{theorem_id}.json"))
    for milestone in milestones["milestones"]:
        ident = milestone["id"]
        tasks.append((f"/milestones/{ident}/history?limit=100&offset=0", f"history-{ident}.json"))
    tasks.append((f"/missions/{MISSION}/comments?limit=100&offset=0", "comments-current.json"))
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        futures = [pool.submit(snapshot, path, token, filename) for path, filename in tasks]
        for future in concurrent.futures.as_completed(futures):
            future.result()
    for theorem_id in theorem_ids:
        theorem = json.loads((EVIDENCE / f"current-{theorem_id}.json").read_text(encoding="utf-8"))["data"]
        attempts = json.loads((EVIDENCE / f"submissions-{theorem_id}.json").read_text(encoding="utf-8"))["data"]
        print(json.dumps({"name": theorem["theorem_name"], "status": theorem["status"],
                          "attempts": [{"id": a.get("id"), "status": a.get("status")}
                                       for a in attempts.get("submissions", [])]}), flush=True)


def targets():
    result = {}
    for path in EVIDENCE.glob("current-*.json"):
        data = json.loads(path.read_text(encoding="utf-8"))["data"]
        result[data["theorem_name"].split(".", 1)[1]] = data
    return result


def submit(token, names):
    known = targets()
    entries = json.loads(MANIFEST.read_text(encoding="utf-8")) if MANIFEST.exists() else []
    for name in names:
        target = known[name]
        source = ROOT / f"Solutions/Sol_ZipfLaw_{name}.lean"
        code = source.read_text(encoding="utf-8")
        if re.search(r"\b(sorry|admit|axiom)\b", code):
            raise RuntimeError(f"Unproved placeholder in {source.name}")
        if "theorem solution" not in code or "import Theorems." in code:
            raise RuntimeError(f"Unexpected solution structure: {source.name}")
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        if any(e["theorem_id"] == target["theorem_id"] and e["sha256"] == digest
               and e.get("status") in ("PENDING", "ACCEPTED") for e in entries):
            print(f"{name}: already submitted", flush=True)
            continue
        explanation = ROOT / f"missions/zipf/explanations/{name}.md"
        fields = {"theorem_id": target["theorem_id"], "proof_type": "prove",
                  "explanation": explanation.read_text(encoding="utf-8")}
        body, ctype = api._multipart(fields, {"file": (source.name, code)})
        response = request("POST", "/verify", token, raw_body=body, ctype=ctype)
        entry = {"name": name, "theorem_id": target["theorem_id"],
                 "source": source.relative_to(ROOT).as_posix(), "sha256": digest,
                 "submitted_at": datetime.now(timezone.utc).isoformat(), **response}
        entries.append(entry)
        save(MANIFEST, entries)
        print(json.dumps({"name": name, **response}), flush=True)


def poll(token):
    entries = json.loads(MANIFEST.read_text(encoding="utf-8"))
    for entry in entries:
        if entry.get("status") != "PENDING":
            continue
        ident = entry["submission_id"]
        result = snapshot(f"/verify?submission_id={ident}", token, f"verdict-{ident}.json")
        entry["status"] = result["status"]
        entry["last_checked_at"] = datetime.now(timezone.utc).isoformat()
        save(MANIFEST, entries)
        print(json.dumps({"name": entry["name"], "submission_id": ident,
                          "status": result["status"], "error_message": result.get("error_message")}), flush=True)


def rate(token):
    scores = {
        "zipf_infinite_extension": (8, "Connects the p-series criterion, zeta normalization, and divergence in one exact statement."),
        "zipfPMF_sum_eq_one": (4, "Basic normalization identity that supports the distribution calculations."),
        "zipfPMF_cdf": (4, "Precisely identifies the cumulative mass, including the empty-prefix boundary."),
        "zipfPMF_mean": (5, "Illustrates the exponent shift that governs all finite moments."),
        "zipfPMF_variance": (5, "Combines the first two shifted moments into the variance formula."),
        "zipfPMF_entropy": (6, "Connects logarithmic probabilities, normalization, and weighted logarithmic sums."),
        "zipfPMF_mode": (4, "States the maximizing rank with an explicit nonnegative-exponent hypothesis."),
        "zipfPMF_ratio": (4, "Isolates the defining rank-frequency relation for arbitrary real exponents."),
        "log_zipfPMF_affine": (5, "Gives the exact affine relation underlying the log-log plot."),
        "zipfMandelbrotPMF_hasSum_one": (6, "Extends finite normalization to a convergent shifted infinite series."),
        "yuleSimon_tail": (8, "A precise asymptotic equivalence obtainable directly from Euler's Gamma limit formula."),
        "monkey_typing_power_law": (8, "Turns word-length counts and sorted enumeration into uniform two-sided power-law bounds."),
        "zipf_one_leadingDigit_benford": (9, "An exact logarithmic-density limit requiring decimal-block counting and control of arbitrary cutoffs.")
    }
    known = targets()
    ratings = [{"theorem_id": known[name]["theorem_id"], "score": score, "reasoning": reasoning}
               for name, (score, reasoning) in scores.items()]
    result = request("POST", "/rate", token, data={"ratings": ratings})
    save(EVIDENCE / "ratings-response.json", result)
    print(json.dumps(result), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("sync", "submit", "poll", "rate"))
    parser.add_argument("names", nargs="*")
    args = parser.parse_args()
    token = api.get_token(force=args.action == "sync")
    # Version only, never credentials or headers.
    if api._load().get("version") != "0.12.4":
        raise RuntimeError("Server version differs from the checked 0.12.4; check API changes first")
    if args.action == "sync":
        sync(token)
    elif args.action == "submit":
        submit(token, args.names)
    elif args.action == "rate":
        rate(token)
    else:
        poll(token)


if __name__ == "__main__":
    main()
