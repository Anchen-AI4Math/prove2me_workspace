"""Publish, prove, audit, and read back the Zipf dependency graph.

Uses the existing API client without exposing credentials. Submissions import
only the explicitly planned, actually referenced, proved child declarations.
"""
import argparse
import concurrent.futures
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urlencode

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
import p2m_api as api
import workspace
from audit import binder_arguments

GRAPH = ROOT / "missions/zipf/graph"
EVIDENCE = ROOT / "missions/zipf/verification"
MANIFEST = EVIDENCE / "graph-submissions.json"
JOBS = EVIDENCE / "graph-publish-jobs.json"


def now():
    return datetime.now(timezone.utc).isoformat()


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


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
    save(EVIDENCE / filename, {"path": path, "fetched_at": now(), "data": data})
    return data


def catalogue(token, plan):
    # Broad keyword search can hit the server's database timeout. Refresh known
    # IDs directly and use the indexed exact-name filter only for new helpers.
    known_ids = {}
    for path in list(EVIDENCE.glob("current-*.json")) + list(EVIDENCE.glob("graph-current-*.json")):
        row = read(path)["data"]
        known_ids[row["theorem_name"].removeprefix("ZipfLaw.")] = row["theorem_id"]
    names = [h["name"] for h in plan["helpers"]] + [r["name"] for r in plan["reductions"]] + plan["independent_roots"] + ["zipfPMF_cdf"]

    def fetch(name):
        if name in known_ids:
            ident = known_ids[name]
            return snapshot(f"/theorems/{ident}", token, f"graph-current-{ident}.json")
        query = urlencode({"theorem_name": "ZipfLaw." + name, "env": plan["env"], "limit": 1, "offset": 0})
        result = snapshot("/theorems?" + query, token, f"graph-search-{name}.json")
        if result["total"] > 1:
            raise RuntimeError("An exact Lean name has multiple declarations in the same environment")
        return result["theorems"][0] if result["theorems"] else None

    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        rows = [row for row in pool.map(fetch, names) if row is not None]
    save(EVIDENCE / "graph-catalogue.json", {"fetched_at": now(), "env": plan["env"], "theorems": rows})
    result = {row["theorem_name"].removeprefix("ZipfLaw."): row for row in rows}
    for helper in plan["helpers"]:
        if helper["name"] in result and result[helper["name"]]["formal_statement"] != helper["formal_statement"]:
            raise RuntimeError("Existing helper name refers to a different exact statement")
    return result


def publish(token, plan):
    audited = read(EVIDENCE / "graph-audit-summary.json")
    if audited["exit_code"] != 0 or not audited["no_sorryAx"]:
        raise RuntimeError("A closed exact-type graph audit is required before publication")
    known = catalogue(token, plan)
    old = read(JOBS) if JOBS.exists() else []
    queued = {job["name"].removeprefix("ZipfLaw.") for job in old}
    problems = [h["problem"] for h in plan["helpers"] if h["name"] not in known and h["name"] not in queued]
    if not problems:
        print("All planned helper statements are published or already queued.")
        return
    result = request("POST", "/submit-problem", token, data={"env": plan["env"], "problems": problems})
    save(EVIDENCE / "graph-publish-response.json", result)
    old.extend({**job, "status": "PENDING", "queued_at": now()} for job in result.get("jobs", []))
    save(JOBS, old)
    print(json.dumps({"jobs": result.get("jobs", []), "errors": result.get("errors", [])}), flush=True)
    if result.get("errors"):
        raise RuntimeError("Some helper statements were not queued")


def publish_poll(token, plan):
    jobs = read(JOBS)
    helpers = {h["name"]: h for h in plan["helpers"]}
    for job in jobs:
        if job.get("status") == "PUBLISHED":
            continue
        result = snapshot(f"/publish-jobs/{job['job_id']}", token, f"graph-job-{job['job_id']}.json")
        job.update(result)
        job["checked_at"] = now()
        if result["status"] == "PUBLISHED":
            helper = helpers[job["name"].removeprefix("ZipfLaw.")]
            target = snapshot(f"/theorems/{result['theorem_id']}", token,
                              f"graph-current-{result['theorem_id']}.json")
            if target["mathlib_rev"] != plan["env"] or target["formal_statement"] != helper["formal_statement"]:
                raise RuntimeError("Published helper statement differs from the audited statement")
            source = target["preamble"] + "\n\n" + target["formal_statement"] + "\n"
            (ROOT / f"Theorems/Thm_{target['theorem_name'].replace('.', '_')}.lean").write_text(source, encoding="utf-8")
        save(JOBS, jobs)
        print(json.dumps({"name": job["name"], "status": result["status"],
                          "theorem_id": result.get("theorem_id"), "error_message": result.get("error_message")}), flush=True)


def submit(token, plan, names):
    known = catalogue(token, plan)
    entries = read(MANIFEST) if MANIFEST.exists() else []
    audit = read(EVIDENCE / "graph-audit-summary.json")
    if audit["exit_code"] != 0 or not audit["no_sorryAx"]:
        raise RuntimeError("The graph proofs need a successful closed exact-type audit")
    audited = {r["source"]: r["sha256"] for r in audit["graph_sources"]}
    for item in plan["helpers"] + plan["reductions"]:
        name = item["name"]
        if names and name not in names:
            continue
        if name not in known:
            print(f"{name}: not published yet", flush=True)
            continue
        target = known[name]
        source = ROOT / item["source"]
        code = source.read_text(encoding="utf-8")
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        if audited.get(item["source"]) != digest:
            raise RuntimeError(f"Proof changed since the closed audit: {source}")
        if any(e["theorem_id"] == target["theorem_id"] and e["sha256"] == digest
               and e.get("status") in ("PENDING", "ACCEPTED") for e in entries):
            print(f"{name}: already submitted", flush=True)
            continue
        if re.search(r"\b(sorry|admit|axiom)\b", code) or "theorem solution" not in code:
            raise RuntimeError(f"Unproved or malformed proof: {source}")
        imports = re.findall(r"^import Theorems\.Thm_ZipfLaw_(\w+)$", code, re.MULTILINE)
        if set(imports) != set(item["dependencies"]) or name in imports:
            raise RuntimeError(f"Unexpected dependency or self-import in {source}")
        if target["mathlib_rev"] != plan["env"]:
            raise RuntimeError("Target environment mismatch")
        unavailable = [dep for dep in imports if dep not in known or known[dep]["status"] != "Proved"]
        if unavailable:
            print(f"{name}: waiting for proved children {unavailable}", flush=True)
            continue
        for dep in imports:
            if not re.search(rf"\b{re.escape(dep)}\b", code.split("theorem solution", 1)[1]):
                raise RuntimeError(f"Unused planned theorem {dep}")
        explanation = (ROOT / item["explanation_file"]).read_text(encoding="utf-8")
        fields = {"theorem_id": target["theorem_id"], "proof_type": "prove", "explanation": explanation}
        body, ctype = api._multipart(fields, {"file": (source.name, code)})
        result = request("POST", "/verify", token, raw_body=body, ctype=ctype)
        entry = {"name": name, "theorem_id": target["theorem_id"], "source": item["source"],
                 "sha256": digest, "submitted_at": now(), "dependencies": item["dependencies"], **result}
        entries.append(entry)
        save(MANIFEST, entries)
        print(json.dumps({"name": name, **result}), flush=True)


def poll(token):
    entries = read(MANIFEST)
    for entry in entries:
        if entry.get("status") != "PENDING":
            continue
        ident = entry["submission_id"]
        result = snapshot(f"/verify?submission_id={ident}", token, f"graph-verdict-{ident}.json")
        entry["status"] = result["status"]
        entry["last_checked_at"] = now()
        save(MANIFEST, entries)
        print(json.dumps({"name": entry["name"], "status": result["status"],
                          "error_message": result.get("error_message")}), flush=True)


def audit(plan):
    # The reference placeholders are never imported. Build closed aliases from
    # the accepted direct proofs before elaborating the reductions unchanged.
    direct_audit = read(EVIDENCE / "audit-summary.json")
    if direct_audit["exit_code"] != 0 or not direct_audit["no_sorryAx"]:
        raise RuntimeError("Run the original direct-proof audit first")
    for record in direct_audit["solutions"]:
        source = ROOT / record["source"]
        name = source.stem.removeprefix("Sol_ZipfLaw_")
        target = (ROOT / f"Theorems/Thm_ZipfLaw_{name}.lean").read_text(encoding="utf-8")
        if (hashlib.sha256(source.read_bytes()).hexdigest() != record["sha256"] or
                hashlib.sha256(target.encode("utf-8")).hexdigest() != record["reference_sha256"]):
            raise RuntimeError("A direct proof or its target changed; rerun scripts/audit.py first")
    base = (EVIDENCE / "ZipfAudit.lean").read_text(encoding="utf-8")
    chunks = ["-- Generated by missions/zipf/scripts/graph.py audit.\n"
              "-- Closed independent mirror of platform declarations; no raw target imports.\n" + base]
    for source in sorted((ROOT / "Solutions").glob("Sol_ZipfLaw_*.lean")):
        name = source.stem.removeprefix("Sol_ZipfLaw_")
        reference = (ROOT / f"Theorems/Thm_ZipfLaw_{name}.lean").read_text(encoding="utf-8")
        declaration = reference.split(f"theorem {name}", 1)[1].split(" := by sorry", 1)[0]
        arguments = binder_arguments(declaration)
        chunks.append(f"namespace ZipfLaw\ntheorem {name} {declaration} := ZipfAudit.{name}.solution {arguments}\nend ZipfLaw\n")
    records = []
    for kind in ("helpers", "reductions"):
        for item in plan[kind]:
            name = item["name"]
            source = ROOT / item["source"]
            code = "\n".join(line for line in source.read_text(encoding="utf-8").splitlines()
                             if not line.startswith("import "))
            reference = item.get("formal_statement") or (ROOT / f"Theorems/Thm_ZipfLaw_{name}.lean").read_text(encoding="utf-8")
            declaration = reference.split(f"theorem {name}", 1)[1].split(" := by sorry", 1)[0]
            arguments = binder_arguments(declaration)
            namespace = f"ZipfGraphAudit.{kind}.{name}"
            chunks.append(f"namespace {namespace}\n{code}\n\nexample {declaration} := solution {arguments}\nend {namespace}\n")
            if kind == "helpers":
                chunks.append(f"namespace ZipfLaw\ntheorem {name} {declaration} := {namespace}.solution {arguments}\nend ZipfLaw\n")
            records.append({"source": item["source"], "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                            "dependencies": item["dependencies"]})
    certificate = ROOT / "Solutions/ZipfLaw/GraphCertificate.lean"
    certificate.parent.mkdir(parents=True, exist_ok=True)
    certificate.write_text("\n".join(chunks), encoding="utf-8")
    lake, env = workspace.lake_environment()
    env["LEAN_NUM_THREADS"] = "1"
    result = subprocess.run([lake, "env", "lean", str(certificate)], cwd=ROOT, env=env,
                            capture_output=True, text=True, encoding="utf-8")
    log = result.stdout + result.stderr
    (EVIDENCE / "graph-audit.log").write_text(log, encoding="utf-8")
    summary = {"checked_at": now(), "exit_code": result.returncode, "no_sorryAx": "sorryAx" not in log,
               "exact_type_checks": True, "graph_sources": records,
               "certificate": certificate.relative_to(ROOT).as_posix(),
               "certificate_sha256": hashlib.sha256(certificate.read_bytes()).hexdigest(),
               "base_audit_sha256": hashlib.sha256((EVIDENCE / "ZipfAudit.lean").read_bytes()).hexdigest(),
               "direct_audit": direct_audit}
    save(EVIDENCE / "graph-audit-summary.json", summary)
    print(log, end="")
    print(f"Audited {len(records)} graph proofs with closed child implementations; exit code {result.returncode}.")
    return result.returncode


def graph_snapshot(token, plan):
    known = catalogue(token, plan)
    names = [h["name"] for h in plan["helpers"]] + [r["name"] for r in plan["reductions"]] + plan["independent_roots"] + ["zipfPMF_cdf"]
    pairs = [(name, known[name]["theorem_id"]) for name in names if name in known]
    tasks = [(f"/theorems/{ident}/{kind}", f"graph-{kind}-{ident}.json")
             for _, ident in pairs for kind in ("graph", "decompositions")]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        for result in pool.map(lambda pair: snapshot(pair[0], token, pair[1]), tasks):
            pass
    entries = read(MANIFEST) if MANIFEST.exists() else []
    checks = []
    for item in plan["helpers"] + plan["reductions"]:
        parent = known[item["name"]]["theorem_id"]
        graph = read(EVIDENCE / f"graph-graph-{parent}.json")["data"]
        decompositions = read(EVIDENCE / f"graph-decompositions-{parent}.json")["data"]["decompositions"]
        accepted = [e for e in entries if e["name"] == item["name"] and e["status"] == "ACCEPTED"]
        for child_name in item["dependencies"]:
            child = known[child_name]["theorem_id"]
            paths = []
            for entry in accepted:
                sid = entry["submission_id"]
                sketch = "sketch-" + sid
                first = [e for e in graph["edges"] if e["source"] == child and e["target"] == sketch]
                second = [e for e in graph["edges"] if e["source"] == sketch and e["target"] == parent]
                if first and second:
                    paths.append({"nodes": [child, sketch, parent], "submission_id": sid,
                                  "edges": [first[0], second[0]]})
            direct = [e for e in graph["edges"] if e["source"] == child and e["target"] == parent]
            if direct:
                paths.append({"nodes": [child, parent], "edges": direct})
            decomposition = any(d["submission_id"] in {e["submission_id"] for e in accepted}
                                and any(c.get("theorem_id") == child for c in d["children"])
                                for d in decompositions)
            checks.append({"parent": item["name"], "parent_id": parent, "child": child_name,
                           "child_id": child, "edge_present": bool(paths), "graph_paths": paths,
                           "accepted_decomposition_present": decomposition,
                           "reduction_submission_ids": [e["submission_id"] for e in accepted]})
    summary = {"checked_at": now(), "edge_direction": "child -> accepted reduction node -> parent", "expected_edges": checks,
               "all_expected_edges_present": all(c["edge_present"] and c["accepted_decomposition_present"] for c in checks),
               "all_theorems_proved": all(known[name]["status"] == "Proved" for name, _ in pairs),
               "all_graph_proofs_accepted": all(any(e["name"] == item["name"] and e["status"] == "ACCEPTED"
                                                    and e["sha256"] == hashlib.sha256((ROOT / item["source"]).read_bytes()).hexdigest()
                                                    for e in entries)
                                                for item in plan["helpers"] + plan["reductions"]),
               "theorems": [{"name": name, "theorem_id": ident, "status": known[name]["status"]} for name, ident in pairs],
               "independent_roots": plan["independent_roots"],
               "forest_roots": ["zipf_infinite_extension", "zipfPMF_entropy", "zipfPMF_mode", "zipfPMF_variance"] + plan["independent_roots"]}
    save(EVIDENCE / "graph-summary.json", summary)
    print(json.dumps({"theorems": len(pairs), "expected_edges": len(checks),
                      "all_expected_edges_present": summary["all_expected_edges_present"]}), flush=True)
    if not (summary["all_expected_edges_present"] and summary["all_theorems_proved"] and summary["all_graph_proofs_accepted"]):
        print(json.dumps([c for c in checks if not c["edge_present"] or not c["accepted_decomposition_present"]]), flush=True)
        return 1
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("audit", "publish", "publish-poll", "submit", "poll", "snapshot"))
    parser.add_argument("names", nargs="*")
    args = parser.parse_args()
    plan = read(GRAPH / "plan.json")
    if args.action == "audit":
        return audit(plan)
    token = api.get_token()
    if api._load().get("version") != "0.12.4":
        raise RuntimeError("Refresh the API documentation for the current deployed version first")
    if args.action == "publish":
        publish(token, plan)
    elif args.action == "publish-poll":
        publish_poll(token, plan)
    elif args.action == "submit":
        submit(token, plan, args.names)
    elif args.action == "poll":
        poll(token)
    else:
        return graph_snapshot(token, plan)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
