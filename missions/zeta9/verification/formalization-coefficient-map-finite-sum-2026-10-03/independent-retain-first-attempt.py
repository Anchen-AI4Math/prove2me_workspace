"""Retain the supplemental interval-binder failure, never modifying author files."""
from pathlib import Path
import json
import shutil

out = Path(__file__).resolve().parent
for name in ["independent-boundary-audit.lean", "independent-boundary-audit.log", "independent-boundary-audit-exit.txt", "independent-compile-receipt.json"]:
    dst = out / (name + ".before-Nat-interval-fix")
    assert not dst.exists()
    shutil.copyfile(out / name, dst)
receipt = json.loads((out / "independent-compile-receipt.json").read_text(encoding="utf-8"))
assert receipt["rows"][-1]["label"] == "independent-boundary-audit" and receipt["rows"][-1]["exit_code"] == 1
receipt["rows"] = receipt["rows"][:-1]
(out / "independent-compile-receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
