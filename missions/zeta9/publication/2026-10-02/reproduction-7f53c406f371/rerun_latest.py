"""Rerun five finite groups without changing the preserved zip."""
import hashlib, json, subprocess, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parent
GROUPS = [('direction_arithmetic_next', 'direction-arithmetic-next-2026-10-02'), ('growing_rank_one_route', 'growing-rank-one-route-2026-10-02'), ('dispersed_pole_frontier', 'dispersed-pole-frontier-2026-10-02'), ('new_linear_form_route', 'new-linear-form-route-2026-10-02'), ('new_linear_form_repair', 'new-linear-form-route-repair-2026-10-02')]
rows = []
for name, directory in GROUPS:
    out = ROOT / "missions/zeta9/verification" / directory
    preserved = {p.name: p.read_bytes() for p in out.glob("*.json")}
    script = ROOT / "missions/zeta9/scripts" / ("verify_" + name + ".py")
    start = time.monotonic()
    run = subprocess.run([sys.executable, str(script)], cwd=ROOT, text=True,
                         encoding="utf-8", errors="replace", capture_output=True)
    comparisons = {name: (out / name).exists() and hashlib.sha256((out / name).read_bytes()).hexdigest() ==
                         hashlib.sha256(data).hexdigest()
                   for name, data in preserved.items()}
    result = {"script": str(script.relative_to(ROOT)).replace(chr(92), "/"),
              "returncode": run.returncode, "elapsed_seconds": round(time.monotonic()-start, 3),
              "preserved_record_sha256": {name:hashlib.sha256(data).hexdigest()
                                           for name,data in preserved.items()},
              "original_json_byte_comparisons": comparisons,
              "stdout": run.stdout, "stderr": run.stderr}
    rows.append(result)
    print(name + ": " + ("PASS" if run.returncode == 0 else "FAIL"), flush=True)
    if run.returncode:
        print(run.stderr, flush=True)
        break
report = {"status": "PASS" if len(rows)==5 and all(r["returncode"]==0 for r in rows) else "FAIL",
          "all_original_json_bytes_identical": all(all(r["original_json_byte_comparisons"].values())
                                                  for r in rows), "groups": rows}
(ROOT / "rerun-report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
if report["status"] != "PASS":
    raise SystemExit(1)
