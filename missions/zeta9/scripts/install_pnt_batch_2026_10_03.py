"""Install frozen canonical modules; preserve the native-vs-statement boundary."""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
OUT = TASK / "formalization/platform/pnt"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    audit = json.loads((OUT / "integration-audit.json").read_text(encoding="utf-8"))
    assert audit["verdict"] == "PASS_OFFLINE_MECHANICAL_FIDELITY"
    targets = json.loads((OUT / "problems-request.json").read_text(encoding="utf-8"))["problems"]
    checks = {row["theorem_name"]: row for row in audit["checks"]}
    copies = []
    for item in targets:
        row = checks[item["theorem_name"]]
        for key, hash_key in (("local_solution", "solution_sha256"), ("local_reference", "reference_sha256")):
            relative = item[key]
            assert relative.startswith(("Solutions/Sol_ZetaNine_HarmonicStability_", "Theorems/Thm_ZetaNine_HarmonicStability_"))
            source = OUT / "staged" / relative
            data = source.read_bytes()
            assert digest(data) == row[hash_key]
            copies.append((source, ROOT / relative, data))
    mirror = OUT / "boundary-mirror/stub/Theorems/Thm_MediumPNT.lean"
    copies.append((mirror, ROOT / "Theorems/Thm_MediumPNT.lean", mirror.read_bytes()))
    # Check every destination first, before performing any write.
    for _, destination, data in copies:
        assert destination.resolve().is_relative_to(ROOT.resolve())
        if destination.exists():
            assert destination.read_bytes() == data, "Preserving differing existing file: " + str(destination)
    rows = []
    for source, destination, data in copies:
        existed = destination.exists()
        if not existed:
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
        assert destination.read_bytes() == data
        rows.append({"source": source.relative_to(TASK).as_posix(),
                     "destination": destination.relative_to(ROOT).as_posix(),
                     "sha256": digest(data), "already_identical": existed})
    scope_path = TASK / "scope.json"
    scope = json.loads(scope_path.read_text(encoding="utf-8"))
    for relative in ("Theorems/Thm_MediumPNT.lean", "missions/zeta9/scripts/install_pnt_batch_2026_10_03.py"):
        if relative not in scope["sources"]:
            scope["sources"].append(relative)
    scope_path.write_text(json.dumps(scope, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    receipt = {"frozen_audit_sha256": digest((OUT / "integration-audit.json").read_bytes()),
               "copies": rows, "shared_source_bytes_match_frozen_stage": True,
               "medium_pnt_mirror_is_proof": False, "native_same_bytes_proof_evidence_preserved": True}
    (OUT / "root-install-receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print("Installed eight exact endpoint modules and one explicit MediumPNT statement mirror.")


if __name__ == "__main__":
    main()
