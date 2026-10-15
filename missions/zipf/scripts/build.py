"""Build the registered Zipf roots with bounded memory use before the mission build."""
import argparse
import concurrent.futures
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
import workspace


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("names", nargs="*")
    parser.add_argument("--workers", type=int, default=2, choices=(1, 2))
    args = parser.parse_args()
    scope = workspace.read_scope("zipf")
    sources = workspace.build_targets(scope)
    if args.names:
        wanted = {f"Solutions/Sol_ZipfLaw_{name}.lean" for name in args.names}
        if not wanted.issubset(set(sources)):
            raise RuntimeError("Requested file is outside the Zipf build scope")
        sources = [source for source in sources if source in wanted]
    lake, env = workspace.lake_environment()
    env["LEAN_NUM_THREADS"] = "1"
    evidence = ROOT / "missions/zipf/verification"

    def build(source):
        module = "+" + source[:-5].replace("/", ".")
        result = subprocess.run([lake, "build", module], cwd=ROOT, env=env,
                                capture_output=True, text=True, encoding="utf-8")
        log = result.stdout + result.stderr
        (evidence / (Path(source).stem + ".build.log")).write_text(log, encoding="utf-8")
        record = {"source": source, "sha256": hashlib.sha256((ROOT / source).read_bytes()).hexdigest(),
                  "exit_code": result.returncode, "no_sorryAx": "sorryAx" not in log}
        print(json.dumps(record), flush=True)
        if result.returncode:
            print(log, flush=True)
        return record

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        records = list(pool.map(build, sources))
    (evidence / "build-summary.json").write_text(json.dumps(records, indent=2) + "\n", encoding="utf-8")
    return int(any(record["exit_code"] or not record["no_sorryAx"] for record in records))


if __name__ == "__main__":
    raise SystemExit(main())
