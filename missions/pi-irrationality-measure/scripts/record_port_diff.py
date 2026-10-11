"""Record the complete current patch without altering any original source."""
import difflib
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
changes = []
patch = []
for staged in sorted((TASK / "port/lean").rglob("*.lean")):
    relative = staged.relative_to(TASK / "port/lean")
    original = TASK / "source/lean" / relative
    source_bytes = original.read_bytes() if original.exists() else b""
    current_bytes = staged.read_bytes()
    source = source_bytes.decode("utf-8").replace("\r\n", "\n")
    current = current_bytes.decode("utf-8").replace("\r\n", "\n")
    if source != current:
        changes.append({"module": str(relative), "new_module": not original.exists(),
                        "original_sha256": hashlib.sha256(source_bytes).hexdigest(),
                        "port_sha256": hashlib.sha256(current_bytes).hexdigest()})
        patch.extend(difflib.unified_diff(source.splitlines(keepends=True),
                                        current.splitlines(keepends=True),
                                        fromfile="source/lean/" + str(relative),
                                        tofile="port/lean/" + str(relative)))
(TASK / "port/current.diff").write_text("".join(patch), encoding="utf-8")
(TASK / "port/changes.json").write_text(json.dumps(changes, indent=2), encoding="utf-8")
print("Recorded", len(changes), "changed/new modules")
