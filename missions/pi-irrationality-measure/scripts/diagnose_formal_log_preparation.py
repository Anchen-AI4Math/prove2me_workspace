"""Read-only diff of current f1 publisher pins against saved offline preparation.

This script calls only publish_formal_log_proof_node.prepare(..., write=False).
It never imports the API client, reads credentials, writes files, or makes
network requests. A mismatch report includes exact nested field differences
and flags same-file paths differing only in the Windows drive-letter case.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import ntpath
import sys
import traceback

import publish_formal_log_proof_node as publisher

EXPECTED_PUBLISHER_SHA256 = "bfe1d7333ba1b263577a7ade8ac777651877f1471ac173d56aa821eee20b95e2"
EXPECTED_HELPER_SHA256 = "8adf3e87f2dc8f7b219cfd55364e3cca391307ffacd46fc6e8d3b12773da7a4f"


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def samefile(left: str, right: str) -> bool:
    try:
        return os.path.samefile(left, right)
    except (OSError, ValueError):
        return False


def drive_case_normalized(value: str) -> str:
    drive, tail = ntpath.splitdrive(value)
    if len(drive) == 2 and drive[1] == ":":
        drive = drive[0].lower() + ":"
    return drive + tail


def is_drive_case_alias(left: str, right: str) -> bool:
    return (left != right and drive_case_normalized(left) == drive_case_normalized(right)
            and samefile(left, right))


def comparable(value):
    if isinstance(value, dict):
        return {key: comparable(item) for key, item in value.items() if key != "prepared_at_utc"}
    if isinstance(value, list):
        if all(isinstance(row, dict) and set(row) == {"path", "sha256"} for row in value):
            return {drive_case_normalized(row["path"]): row["sha256"] for row in value}
        return [comparable(item) for item in value]
    return value


def diff(saved, current, path="$", out=None):
    if out is None:
        out = []
    if isinstance(saved, dict) and isinstance(current, dict):
        for key in sorted(set(saved) | set(current)):
            if key == "prepared_at_utc":
                continue
            child = f"{path}.{key}"
            if key not in saved:
                out.append({"field": child, "saved": "<missing>", "current": current[key]})
            elif key not in current:
                out.append({"field": child, "saved": saved[key], "current": "<missing>"})
            else:
                diff(saved[key], current[key], child, out)
        return out
    if isinstance(saved, list) and isinstance(current, list):
        if all(isinstance(row, dict) and set(row) == {"path", "sha256"} for row in saved + current):
            old = {drive_case_normalized(row["path"]): row for row in saved}
            new = {drive_case_normalized(row["path"]): row for row in current}
            for key in sorted(set(old) | set(new)):
                if key not in old:
                    out.append({"field": path, "path": new[key]["path"], "saved": "<missing>",
                                "current_sha256": new[key]["sha256"]})
                elif key not in new:
                    out.append({"field": path, "path": old[key]["path"], "saved_sha256": old[key]["sha256"],
                                "current": "<missing>"})
                elif old[key]["path"] != new[key]["path"] or old[key]["sha256"] != new[key]["sha256"]:
                    old_path, new_path = old[key]["path"], new[key]["path"]
                    alias = is_drive_case_alias(old_path, new_path)
                    out.append({"field": path, "saved_path": old_path, "current_path": new_path,
                                "saved_sha256": old[key]["sha256"], "current_sha256": new[key]["sha256"],
                                "samefile_drive_letter_case_only": alias})
            return out
        if len(saved) != len(current):
            out.append({"field": path, "saved_length": len(saved), "current_length": len(current)})
        for index, (left, right) in enumerate(zip(saved, current)):
            diff(left, right, f"{path}[{index}]", out)
        return out
    if saved != current:
        out.append({"field": path, "saved": saved, "current": current})
    return out


def captured_prepare_locals(error):
    tb = error.__traceback__
    while tb is not None:
        frame = tb.tb_frame
        if frame.f_code is publisher.prepare.__code__:
            return frame.f_locals
        tb = tb.tb_next
    return {}


def main() -> int:
    publisher_path = Path(publisher.__file__).resolve()
    helper_path = Path(publisher.securitypins.__file__).resolve()
    publication_dir = publisher.DEFAULT_STAGE / "publication"
    preparation_path = publication_dir / "preparation.json"
    report = {
        "schema_version": 1,
        "artifact_kind": "formal-log-offline-preparation-readonly-diagnostic",
        "network_used": False,
        "api_client_imported": False,
        "publisher_path": str(publisher_path),
        "publisher_sha256": sha(publisher_path),
        "expected_publisher_sha256": EXPECTED_PUBLISHER_SHA256,
        "security_helper_path": str(helper_path),
        "security_helper_sha256": sha(helper_path),
        "expected_security_helper_sha256": EXPECTED_HELPER_SHA256,
        "preparation_path": str(preparation_path),
        "preparation_sha256": sha(preparation_path) if preparation_path.is_file() else None,
        "publication_record_exists": (publication_dir / "publication.json").exists(),
    }
    if report["publisher_sha256"] != EXPECTED_PUBLISHER_SHA256:
        report["error"] = "Publisher differs from the frozen SHA; refusing diagnostic replay"
        print(json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2))
        return 2
    if report["security_helper_sha256"] != EXPECTED_HELPER_SHA256:
        report["error"] = "Security helper differs from the frozen SHA; refusing diagnostic replay"
        print(json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2))
        return 2
    if not preparation_path.is_file():
        report["error"] = "Saved offline preparation is missing"
        print(json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2))
        return 2
    saved = publisher.read(preparation_path)
    try:
        result = publisher.prepare(publisher.DEFAULT_STAGE, publisher.DEFAULT_METADATA, write=False)
        current = result[5]
        report["offline_preparation_matches"] = comparable(saved) == comparable(current)
        report["differences"] = diff(saved, current)
        report["payload_files_match"] = all(
            (publication_dir / name).is_file()
            and not (publication_dir / name).is_symlink()
            and (publication_dir / name).read_bytes() == data
            for name, data in result[6].items())
        report["result"] = "current pins match saved preparation"
    except Exception as error:
        local = captured_prepare_locals(error)
        current = local.get("pins")
        report["offline_preparation_matches"] = False
        report["error_type"] = type(error).__name__
        report["error"] = str(error)
        report["traceback"] = "".join(traceback.format_exception(type(error), error, error.__traceback__))
        if isinstance(current, dict):
            report["current_security_pin_count"] = len(current.get("security_pins", []))
            report["differences"] = diff(saved, current)
            current_metadata = current.get("metadata_sha256")
            report["current_metadata_sha256"] = current_metadata
        report["result"] = "preparation refused; no files written and no API used"
    print(json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
