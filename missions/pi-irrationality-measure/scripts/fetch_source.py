"""Fetch only OpenAI family 017's real Lean import closure, pinned to a commit."""
import hashlib
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import re
import subprocess
import sys
import threading
import urllib.request

sys.stdout.reconfigure(encoding="utf-8")
TASK = Path(__file__).resolve().parents[1]
DEST = TASK / "source"
OPENER = urllib.request.build_opener(urllib.request.ProxyHandler({"https": "http://127.0.0.1:65532"}))
state_path = DEST / "manifest.json"
if state_path.exists():
    sha = json.loads(state_path.read_text(encoding="utf-8"))["commit"]
else:
    result = subprocess.run(["git", "-c", "http.proxy=http://127.0.0.1:65532", "ls-remote",
                             "https://github.com/openai/math.git", "refs/heads/main"],
                            capture_output=True, text=True, check=True)
    sha = result.stdout.split()[0]
DEST.mkdir(parents=True, exist_ok=True)
manifest = {"repository": "https://github.com/openai/math", "commit": sha, "files": {}}
state_lock = threading.Lock()
state_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")


def fetch(path):
    local = DEST / path
    if not local.exists():
        url = f"https://raw.githubusercontent.com/openai/math/{sha}/{path}"
        with OPENER.open(url, timeout=40) as response:
            data = response.read()
        local.parent.mkdir(parents=True, exist_ok=True)
        local.write_bytes(data)
    data = local.read_bytes()
    with state_lock:
        manifest["files"][path] = {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
        state_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return data.decode("utf-8")


queue = ["OAI.NumberTheory.PiExponent.Main"]
seen = set()
with ThreadPoolExecutor(max_workers=8) as executor:
    while queue:
        batch = []
        while queue and len(batch) < 8:
            module = queue.pop(0)
            if module in seen:
                continue
            seen.add(module)
            path = "lean/" + module.replace(".", "/") + ".lean"
            batch.append((path, executor.submit(fetch, path)))
        for path, future in batch:
            source = future.result()
            for line in source.splitlines():
                match = re.match(r"(?:public\s+)?import\s+(.+)", line)
                if match:
                    for dep in match.group(1).split():
                        if dep.startswith("OAI."):
                            queue.append(dep)
                        elif dep.startswith(("Mathlib", "Lean", "Std", "Init")):
                            pass
                        else:
                            raise RuntimeError(f"External dependency to inspect: {dep}")
        print("Fetched", len(manifest["files"]), "modules; queued imports", len(queue), flush=True)
for path in ["lean/docs/017.md", "lean/ComparatorChallenges/PiExponent.lean",
             "lean/ComparatorChallenges/PiExponent.json", "lean/lean-toolchain",
             "lean/lakefile.lean", "LICENSE"]:
    fetch(path)
print("COMMIT", sha, "MODULES", len(seen))
