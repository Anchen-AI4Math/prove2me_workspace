"""Version-pinned, read-only checkpoint before the new public mission proposal."""
from __future__ import annotations
import hashlib
import json
import sys
import urllib.request
from pathlib import Path
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor
import inspect_platform_progress_2026_10_03 as inspector
import publish_mission_2026_10_02 as api

TASK = Path(__file__).resolve().parents[1]
DOCS = TASK / "formalization/platform/readback-2026-10-07/api-docs-v0.12.1"
OUT = TASK / "publication/2026-10-07/new-public-mission/preflight"
BASE = "https://raw.githubusercontent.com/prove2me/prove2me_workspace/v0.12.1/"
PINS = {
    "SKILL.md": "6693ed2a822a415b84bfb59240c1504895cda267a46ea348de9cd0a1905131e6",
    "references/mission_captain.md": "85be7ad6e2a9ff1ed70a5100b01c436270660accd36f81e1a16039b7282cfe3e",
    "references/missions.md": "6064c213b1ab65eac8da26f8834efbfa013da60a592b6c6201c702383be86fa9",
    "references/prove.md": "8b231b0494719c4a90abc95687fcd183a24cfcb0636ddcfd9de050d9f5146a18",
    "references/contribute.md": "0c21104fdec143aef4d1dacb208f528b4a1068050a77af642bc1e21cb1471ce1",
    "references/setup.md": "fca66035b392f696238882ffc4113bf625f0d266402b90e3f0d36d541bad8363",
}

def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")

def docs():
    for name, expected in PINS.items():
        assert hashlib.sha256((DOCS/name).read_bytes()).hexdigest() == expected, name
    previous = TASK / "formalization/platform/readback-2026-10-04/api-docs-v0.11.8"
    same = []
    for name in ["mission_captain", "missions", "prove", "contribute"]:
        relative = "references/"+name+".md"
        assert (DOCS/relative).read_bytes() == (previous/relative).read_bytes(), relative
        same.append(relative)
    fetched = []
    for relative in ["references/mission_description.md", "references/upload_full_project.md"]:
        target = DOCS/relative
        if not target.exists():
            with urllib.request.urlopen(BASE+relative, timeout=40) as response:
                target.write_bytes(response.read())
        fetched.append({"path": relative, "url": BASE+relative,
                        "sha256": hashlib.sha256(target.read_bytes()).hexdigest()})
    save(OUT/"version-compatibility.json", {"checked_at": datetime.now(timezone.utc).isoformat(),
        "version": "0.12.1", "health_and_refresh_version_guards_preserved": True,
        "official_redirect_boundary_preserved": True, "pins": PINS,
        "endpoint_documents_byte_identical_to_reviewed_0_11_8": same, "additional_documents": fetched})

def audit():
    docs()
    assert not (OUT/"progress-audit.json").exists(), "Preserve an existing checkpoint"
    inspector.EXPECTED_VERSION = "0.12.1"
    inspector.DOCS = DOCS
    inspector.OUT = OUT
    inspector.inspect()
    client = api.Client()
    milestone_rows = json.loads((OUT/"milestones.json").read_text(encoding="utf-8"))
    identifiers = {"523f37b8-ae98-406c-a3f7-43aa8e002dd7"}
    identifiers.update(row["theorem"]["id"] for row in milestone_rows if row.get("theorem"))
    results = json.loads((OUT/"progress-audit.json").read_text(encoding="utf-8"))["existing_handles"]
    identifiers.update(row["theorem_id"] for row in results if row.get("theorem_id") and row["status"].upper() == "PUBLISHED")
    def read(identifier):
        value = client.call("GET", "/theorems/"+identifier)
        save(OUT/"canonical"/(identifier+".json"), value)
        return {"id": identifier, "status": value.get("status"), "visibility": value.get("visibility"),
                "name": value.get("theorem_name"), "is_definition": value.get("is_definition")}
    with ThreadPoolExecutor(max_workers=4) as pool:
        canonical = list(pool.map(read, sorted(identifiers)))
    save(OUT/"canonical-index.json", canonical)
    proposals = client.call("GET", "/mission-proposals?limit=20&offset=0")
    save(OUT/"own-proposals.json", proposals)
    print(json.dumps({"canonical_readbacks":len(canonical), "new_mission_writes":0}, ensure_ascii=False),flush=True)

if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if len(sys.argv)>1 and sys.argv[1] == "docs":
        docs()
        print("Pinned v0.12.1 compatibility and additional official documents saved")
    else:
        audit()
