"""Preserve and correct an independent oracle's initially too narrow ref filter."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
HERE=Path(__file__).resolve().parent
PROJECT=HERE / "project"
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for filename in ["sketch_info.jsonl"]:
    (HERE / (filename+".before-namespace-filter-fix")).write_bytes((HERE / filename).read_bytes())
validation=subprocess.run([sys.executable,str(HERE / "check_reconstruction.py")],cwd=HERE,capture_output=True)
(HERE / "reconstruction-narrow-filter.log").write_bytes(validation.stdout+validation.stderr)
(HERE / "reconstruction-narrow-filter-exit.txt").write_text(str(validation.returncode)+"\n",encoding="utf-8")
assert validation.returncode == 1
env=os.environ.copy();env.pop("LEAN_PATH",None)
command=["lake","env","lean","--run","extract_sketch_info.lean","missions/zeta9/formalization/CoefficientMapJet.lean","ZetaNine"]
p=subprocess.run(command,cwd=PROJECT,env=env,capture_output=True)
(HERE / "stage2-extract-corrected.log").write_bytes(p.stdout+p.stderr)
(HERE / "stage2-extract-corrected-stderr.log").write_bytes(p.stderr)
(HERE / "stage2-extract-corrected-exit.txt").write_text(str(p.returncode)+"\n",encoding="utf-8")
if p.returncode:print((p.stdout+p.stderr).decode("utf-8-sig"),flush=True)
assert p.returncode == 0
(HERE / "sketch_info.jsonl").write_bytes(p.stdout)
facts=[json.loads(s) for s in p.stdout.decode("utf-8-sig").splitlines() if s.startswith("{")]
receipt={"reason":"Independent initial namespace filter ZetaNine.CoefficientMapJet omitted eleven actual Base references. The original author filter ZetaNine is required to include the genuine cross-module closure; no author or mathematical source changed.","initial_filter":"ZetaNine.CoefficientMapJet","initial_Lean_exit_code":0,"initial_refs":130,"initial_facts":"sketch_info.jsonl.before-namespace-filter-fix","initial_fact_sha256":sha(HERE / "sketch_info.jsonl.before-namespace-filter-fix"),"validation_exit_code":validation.returncode,"validation_log_sha256":sha(HERE / "reconstruction-narrow-filter.log"),"corrected_command":command,"working_directory":str(PROJECT),"corrected_Lean_exit_code":p.returncode,"final_fact_counts":{k:sum(f["kind"]==k for f in facts) for k in ["decl","ref","command"]},"final_facts_sha256":sha(HERE / "sketch_info.jsonl"),"corrected_log_sha256":sha(HERE / "stage2-extract-corrected.log")}
(HERE / "stage2-prefix-correction-receipt.json").write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print(json.dumps(receipt,ensure_ascii=False),flush=True)
