"""Retain supplemental function-unfolding failure; author freezes are read only."""
from pathlib import Path
import json
import shutil

out = Path(__file__).resolve().parent
for name in ["independent-boundary-audit.lean", "independent-boundary-audit.log", "independent-boundary-audit-exit.txt", "independent-compile-receipt.json"]:
    dst = out / (name + ".before-function-unfold-fix")
    assert not dst.exists()
    shutil.copyfile(out / name, dst)
receipt = json.loads((out / "independent-compile-receipt.json").read_text(encoding="utf-8"))
assert len(receipt["rows"]) == 10 and receipt["rows"][-1]["label"] == "independent-boundary-audit" and receipt["rows"][-1]["exit_code"] == 1
receipt["rows"] = receipt["rows"][:-1]
(out / "independent-compile-receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
