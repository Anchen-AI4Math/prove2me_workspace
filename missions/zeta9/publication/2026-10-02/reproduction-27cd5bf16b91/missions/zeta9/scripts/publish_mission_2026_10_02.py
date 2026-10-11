"""In-place, read-back-checked publication of the existing zeta9 mission.

Credentials are read only for official Prove2me API operations, never printed,
copied into artifacts, or saved here. The default mode is read-only snapshot.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = ROOT.parents[1]
OUT = ROOT / "publication/2026-10-02"
BASE = "https://prove2.me/api/v1"
VERSION = "0.11.6"
MISSION = "8195d8fe-059f-4515-92b4-57b585e2bac6"
PROPOSAL = "06faf23f-00c2-4edf-92ab-1212cdb7d7d6"
NAME = "Irrationality of ζ(9): weighted lattice route"


def save(name, value):
    path = OUT / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


class OfficialRedirects(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, fp, code, msg, headers, newurl):
        if not newurl.startswith(BASE + "/"):
            raise RuntimeError("Refusing an authenticated redirect outside the official API")
        return super().redirect_request(request, fp, code, msg, headers, newurl)


class Client:
    def __init__(self):
        self.opener = urllib.request.build_opener(OfficialRedirects())
        health = self.call("GET", "/health", authenticated=False)
        if health.get("version") != VERSION:
            raise RuntimeError("Platform version changed; review the matching API docs first")
        credentials = json.loads((WORKSPACE / "credentials.json").read_text(encoding="utf-8"))
        self.token = credentials.get("access_token")
        if not self.token or credentials.get("expires_at", 0) <= time.time() + 120:
            refreshed = self.call("POST", "/agent/refresh", {"api_key": credentials["api_key"]}, authenticated=False)
            if refreshed.get("version") != VERSION:
                raise RuntimeError("Token refresh returned an unreviewed platform version")
            self.token = refreshed.get("access_token") or refreshed.get("token")
        if not self.token:
            raise RuntimeError("No usable Prove2me access token")

    def call(self, method, path, data=None, authenticated=True):
        assert path.startswith("/")
        headers = {"Content-Type": "application/json"}
        if authenticated:
            headers["Authorization"] = "Bearer " + self.token
        body = None if data is None else json.dumps(data, ensure_ascii=False).encode("utf-8")
        request = urllib.request.Request(BASE + path, data=body, headers=headers, method=method)
        for attempt in range(4 if method == "GET" else 1):
            try:
                with self.opener.open(request, timeout=40) as response:
                    return json.load(response)
            except urllib.error.HTTPError as error:
                # Never echo request bodies or credentials when authentication fails.
                raise RuntimeError(f"Prove2me {method} {path} returned HTTP {error.code}") from None
            except urllib.error.URLError:
                if method != "GET" or attempt == 3:
                    raise RuntimeError(f"Network failure for {method} {path}; check remote state before retrying a write") from None
                time.sleep(1 + attempt)

    def mission(self):
        for offset in range(0, 10000, 100):
            page = self.call("GET", f"/missions?limit=100&offset={offset}")
            rows = page.get("missions", [])
            found = next((row for row in rows if row.get("id") == MISSION), None)
            if found:
                assert found["name"] == NAME, found["name"]
                return found
            if len(rows) < 100:
                break
        raise RuntimeError("The specified existing mission was not found for this account")

    def snapshot(self, folder):
        mission = self.mission()
        save(folder + "/mission.json", mission)
        milestones = self.call("GET", f"/missions/{MISSION}/milestones?limit=200&offset=0")
        proposal = self.call("GET", f"/mission-proposals/{PROPOSAL}")
        comments = self.call("GET", f"/missions/{MISSION}/comments?limit=100&offset=0")
        save(folder + "/milestones.json", milestones)
        save(folder + "/proposal.json", proposal)
        save(folder + "/comments.json", comments)
        theorem = mission.get("main_theorem", {})
        goal_id = theorem.get("theorem_id") or theorem.get("id")
        if goal_id:
            goal = self.call("GET", "/theorems/" + goal_id)
            graph = self.call("GET", "/theorems/" + goal_id + "/graph")
            save(folder + "/goal.json", goal)
            save(folder + "/graph.json", graph)
        print(json.dumps({"mission_id": MISSION, "name": mission["name"],
                          "visibility": mission.get("visibility"),
                          "release_requested_at": mission.get("release_requested_at"),
                          "proposal_status": proposal.get("status"),
                          "main_theorem": theorem,
                          "milestones": len(milestones.get("milestones", [])),
                          "completed_milestones": sum(bool(x.get("completed")) for x in milestones.get("milestones", []))},
                         ensure_ascii=False, indent=2))
        return mission, milestones, proposal, comments

    def sync(self):
        before = self.mission()
        description = (OUT / "mission-description.md").read_text(encoding="utf-8")
        result = self.call("PATCH", "/missions/" + MISSION, {"description": description})
        save("mission-update-response.json", result)
        after = self.mission()
        assert after["description"] == description
        assert after["name"] == before["name"] and after["main_theorem"] == before["main_theorem"]
        plan = json.loads((OUT / "milestone-updates.json").read_text(encoding="utf-8"))
        current = self.call("GET", f"/missions/{MISSION}/milestones?limit=200&offset=0")["milestones"]
        by_id = {row["id"]: row for row in current}
        receipts = []
        for entry in plan:
            row = by_id[entry["id"]]
            assert row.get("theorem") is None, "Do not rewrite linked canonical milestones"
            patch = {key: entry[key] for key in ("title", "milestone_description", "reason")}
            if row["title"] == patch["title"] and row["milestone_description"] == patch["milestone_description"]:
                continue
            result = self.call("PATCH", "/milestones/" + entry["id"], patch)
            receipts.append(result)
            save("milestone-update-responses.json", receipts)
            print("Updated research milestone:", patch["title"], flush=True)
        checked = self.call("GET", f"/missions/{MISSION}/milestones?limit=200&offset=0")["milestones"]
        checked_by_id = {row["id"]: row for row in checked}
        for entry in plan:
            assert checked_by_id[entry["id"]]["title"] == entry["title"]
            assert checked_by_id[entry["id"]]["milestone_description"] == entry["milestone_description"]
        comment = (OUT / "mission-comment.md").read_text(encoding="utf-8")
        comments = self.call("GET", f"/missions/{MISSION}/comments?limit=100&offset=0")["comments"]
        existing = next((row for row in comments if row.get("body_md") == comment), None)
        if not existing:
            existing = self.call("POST", f"/missions/{MISSION}/comments", {"body_md": comment, "tags": ["reference", "strategy"]})
        save("research-handoff-comment.json", existing)
        checked_comments = self.call("GET", f"/missions/{MISSION}/comments?limit=100&offset=0")["comments"]
        assert any(row.get("body_md") == comment for row in checked_comments)
        save("sync-receipt.json", {"mission_id": MISSION, "description_sha256": hashlib.sha256(description.encode()).hexdigest(),
                                   "milestone_updates_requested": len(plan), "milestone_updates_applied": len(receipts),
                                   "comment_id": existing.get("id"), "readback_verified": True, "api_version": VERSION})
        print("Mission metadata, research milestones and handoff comment: read-back PASS")

    def release(self):
        assert (OUT / "sync-receipt.json").exists(), "Sync and verify concrete materials first"
        before = self.mission()
        if before.get("visibility") == "public" or before.get("release_requested_at"):
            save("release-response.json", {"already_requested_or_public": True, "mission": before})
        else:
            response = self.call("POST", f"/missions/{MISSION}/make-public", {})
            save("release-response.json", response)
        self.snapshot("platform-after")


def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("snapshot", "sync", "release"), nargs="?", default="snapshot")
    args = parser.parse_args()
    client = Client()
    if args.mode == "snapshot":
        client.snapshot("platform-before")
    elif args.mode == "sync":
        client.sync()
    else:
        client.release()


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        raise SystemExit(str(error)) from None
