"""Two remaining real controls, serial only after source-chunk worker is terminal."""
from pathlib import Path
import json, subprocess, sys
sys.stdout.reconfigure(encoding="utf8")
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=OUT.parents[3]
for mode,file,count in [("audit","IndependentBoundaries.lean",11),("resolver","IndependentResolverV2.lean",20)]:
    print("START remaining actual control",file,flush=True)
    result=subprocess.run([sys.executable,str(OUT/"run_after_lane_grant_v2.py"),mode,"--file",file,"--lane-grant","ROOT_EXPLICIT_LANE_GRANT"],cwd=TASK)
    receipt=json.loads((OUT/"actual-execution-receipt.json").read_text(encoding="utf8"))
    row=receipt["rows"][-1]
    assert row["file"]==file
    if result.returncode!=0:
        log=(ROOT/row["log"]["root_relative"]).read_text(encoding="utf8")
        print("RETAINED genuine control failure",file,"exit",row["actual_exit"],flush=True)
        print(log[:14000],flush=True)
        raise SystemExit(result.returncode)
    records=[json.loads(line) for line in (ROOT/row["log"]["root_relative"]).read_text(encoding="utf8").splitlines() if line.startswith("{")]
    assert len(records)==count,(file,len(records),count)
    print("COMPLETE actual control",file,"records",len(records),flush=True)
print("Both genuine final controls terminal actual0",flush=True)
