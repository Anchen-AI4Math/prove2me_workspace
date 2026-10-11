"""Resume-safe release upload of the separately frozen advanced proof sources."""
from __future__ import annotations

import hashlib
import argparse
import json
from pathlib import Path, PurePosixPath
import subprocess
from datetime import datetime, timezone
import zipfile


TASK = Path(__file__).resolve().parents[1]
OUT = TASK / "publication/2026-10-02/advanced-proofs"
REPO = "Anchen0823/zeta9-research-notes"
TAG = "research-2026-10-02"
ARCHIVE = "zeta9-advanced-proofs-2026-10-02.zip"
EXPECTED = "87c7ea2680bda568e8e2b36b82f48dab6910ab9bf92e8b4486471c547792e31c"
OLD = {
    "zeta9-research-2026-10-02.zip": (7756223, "68a821653ae08e4f0b2917c770215dfbe60af2670ea3cb6a87521f75b665f2a0"),
    "zeta9-formal-proofs-2026-10-02.zip": (81079, "50e1058a1c44f65271837a1943bc0a0a7c80385c941413d284e7dcb70ad82405"),
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def save(name: str, data) -> None:
    (OUT / name).write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def gh(*args: str) -> str:
    result = subprocess.run(["gh", *args], check=False, capture_output=True, text=True, encoding="utf-8")
    if result.returncode:
        # gh errors contain no credential material; this script never reads credentials.
        raise RuntimeError(f"gh command failed ({result.returncode}): {result.stderr.strip()}")
    return result.stdout


def release():
    return json.loads(gh("release", "view", TAG, "--repo", REPO, "--json", "url,assets"))


def matching_asset(asset, size: int, digest: str) -> bool:
    return asset["size"] == size and asset.get("digest") == "sha256:" + digest


def check_old(data) -> None:
    assets = {a["name"]: a for a in data["assets"]}
    for name, (size, digest) in OLD.items():
        assert name in assets and matching_asset(assets[name], size, digest), name


def local_gate():
    validation = json.loads((OUT / "package-validation.json").read_text(encoding="utf-8"))
    assert validation["status"] == "PASS" and validation["build_exit_code"] == 0
    assert validation["actual_axiom_audit_declarations"] == 16
    assert set(validation["actual_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
    final = json.loads((OUT / "final-delivery-check.json").read_text(encoding="utf-8"))
    assert final["status"] == "PASS" and final["extraction_status"] == "PASS"
    for item in final["sidecar_checks"]:
        assert item["pass"] and sha((OUT / item["file"]).read_bytes()) == item["sha256"]
    independent = json.loads((OUT / "independent-release-review.json").read_text(encoding="utf-8"))
    assert independent["verdict"] == "PASS"
    assert independent["archive_sha256"] == EXPECTED
    assert independent["checks"] and all(c["pass"] for c in independent["checks"])
    archive = OUT / ARCHIVE
    assert sha(archive.read_bytes()) == EXPECTED and archive.stat().st_size == 270644
    manifest_bytes = (OUT / "source-manifest.json").read_bytes()
    manifest = json.loads(manifest_bytes)
    with zipfile.ZipFile(archive) as package:
        assert package.testzip() is None
        names = package.namelist()
        assert len(names) == 81 and len(set(names)) == 81
        assert set(names) == {row["path"] for row in manifest["files"]} | {"source-manifest.json"}
        assert package.read("source-manifest.json") == manifest_bytes
        for row in manifest["files"]:
            path = PurePosixPath(row["path"])
            assert not path.is_absolute() and ".." not in path.parts
            assert not ({".lake", ".git", "__pycache__"} & set(path.parts))
            content = package.read(row["path"])
            assert len(content) == row["bytes"] and sha(content) == row["sha256"], row["path"]
    sidecars = [("README.md", "ADVANCED-PROOFS-README.md"),
                ("SHA256SUMS.txt", "ADVANCED-PROOFS-SHA256SUMS.txt"),
                ("independent-release-review.json", "ADVANCED-PROOFS-INDEPENDENT-REVIEW.json")]
    for src, dst in sidecars:
        content = (OUT / src).read_bytes()
        destination = OUT / dst
        if destination.exists():
            assert destination.read_bytes() == content, dst
        else:
            destination.write_bytes(content)
    return [archive] + [OUT / dst for _, dst in sidecars]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-only", action="store_true", help="Validate local files without GitHub or network operations.")
    args = parser.parse_args()
    paths = local_gate()
    if args.check_only:
        save("local-upload-readiness.json", {"verified": True, "network_operations": False,
             "archive_sha256": EXPECTED, "assets": [{"name": p.name, "bytes": p.stat().st_size,
             "sha256": sha(p.read_bytes())} for p in paths]})
        print("Local frozen archive and four release assets verified; no network operation performed.")
        return
    before = release()
    check_old(before)
    save("release-before-upload.json", before)
    existing = {a["name"]: a for a in before["assets"]}
    missing = []
    for path in paths:
        if path.name in existing:
            assert matching_asset(existing[path.name], path.stat().st_size, sha(path.read_bytes())), path.name
        else:
            missing.append(str(path))
    if missing:
        gh("release", "upload", TAG, *missing, "--repo", REPO)
    after = release()
    check_old(after)
    save("release-after-upload.json", after)
    assets = {a["name"]: a for a in after["assets"]}
    checks = []
    for path in paths:
        asset = assets[path.name]
        digest = sha(path.read_bytes())
        assert matching_asset(asset, path.stat().st_size, digest), path.name
        checks.append({"name": path.name, "bytes": path.stat().st_size, "sha256": digest,
                       "url": asset["url"], "remote_digest_verified": True})
    save("release-upload-receipt.json", {
        "verified": True, "checked_at": datetime.now(timezone.utc).isoformat(),
        "url": assets[ARCHIVE]["url"], "sha256": EXPECTED, "bytes": 270644,
        "release": after["url"], "assets": checks, "earlier_two_archives_unchanged": True,
        "independent_review": "PASS", "platform_acceptance_claimed_by_package": False,
    })
    print("Advanced proof source ZIP and uniquely named sidecars uploaded; remote sizes and SHA256 verified.")
    print(assets[ARCHIVE]["url"])


if __name__ == "__main__":
    main()
