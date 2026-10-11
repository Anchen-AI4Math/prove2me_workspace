"""Make a separate editable copy while retaining pinned original source hashes."""
import json
from pathlib import Path
import shutil
import sys

TASK = Path(__file__).resolve().parents[1]
source = TASK / "source/lean/OAI"
dest = TASK / "port/lean/OAI"
for original in source.rglob("*.lean"):
    staged = dest / original.relative_to(source)
    if not staged.exists():
        staged.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(original, staged)
    text = staged.read_text(encoding="utf-8")
    text = text.replace("import Mathlib.Basic.Real.Basic", "import Mathlib.Data.Real.Basic")
    text = text.replace("import Mathlib.Basic.Complex.Basic", "import Mathlib.Data.Complex.Basic")
    staged.write_text(text, encoding="utf-8")
scope_path = TASK / "scope.json"
scope = json.loads(scope_path.read_text(encoding="utf-8"))
target = ("missions/pi-irrationality-measure/port/lean/OAI/NumberTheory/PiExponent/" +
          (sys.argv[1] if len(sys.argv) > 1 else "Main.lean"))
if target not in scope["build"]:
    scope["build"].append(target)
scope_path.write_text(json.dumps(scope, indent=2) + "\n", encoding="utf-8")
print("Prepared", len(list(dest.rglob("*.lean"))), "Lean source modules")
