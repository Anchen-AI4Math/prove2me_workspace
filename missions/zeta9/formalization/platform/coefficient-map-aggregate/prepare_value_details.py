"""Supplement the already observed main report with proof-visible Expr evidence."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
from embed_definition_fields import create_value_comparison
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;PROJECT=OUT/"project"
NS="ZetaNine.CoefficientMapAggregate";ALIAS="ZetaNine.CoefficientMapAggregateValueComparison"
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):
 if p.name=="native-value-comparison.lean":p=p.with_name("native-value-details.lean")
 p.write_bytes(s if isinstance(s,bytes) else s.encode("utf-8"))
main=json.loads((OUT/"compile-receipt.json").read_text(encoding="utf-8"));assert main["complete"] and len(main["rows"])==50
create_value_comparison({"OUT":OUT,"PROJECT":PROJECT,"NS":NS,"ALIAS_NS":ALIAS,"DEFS":["aggregate","coordinatePolynomial","polynomialCoordinates","aggregateLinearMap","coordinateLinearMap","quarticAggregateLinearMap"],"write":write})
env=os.environ.copy();env.pop("LEAN_PATH",None);env["LEAN_NUM_THREADS"]="1"
p=subprocess.run(["lake","env","lean","native-value-details.lean"],cwd=PROJECT,env=env,capture_output=True)
(OUT/"native-value-details.log").write_bytes(p.stdout+p.stderr);(OUT/"native-value-details-exit.txt").write_text(str(p.returncode)+"\n",encoding="utf-8")
rs=[json.loads(s) for s in p.stdout.decode("utf-8-sig").splitlines() if s.startswith("{")]
record={"actual_exit_code":p.returncode,"command":["lake","env","lean","native-value-details.lean"],"working_directory":str(PROJECT),"source":"native-value-details.lean","source_sha256":sha(OUT/"native-value-details.lean"),"log":"native-value-details.log","log_sha256":sha(OUT/"native-value-details.log"),"exit_file":"native-value-details-exit.txt","exit_file_sha256":sha(OUT/"native-value-details-exit.txt"),"record_count":len(rs),"pp_proofs_enabled":True,"actual_Expr_repr_retained":True,"prior_main_report_preserved":True,"prior_main_report_sha256":sha(OUT/"native-value-comparison.log"),"reason":"Original generic type reports pretty-print some proof fields as dots. Supplement full native comparison evidence without overwriting that actual report."}
(OUT/"native-value-details-receipt.json").write_text(json.dumps(record,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print(json.dumps({"value_details_exit":p.returncode,"records":len(rs)}),flush=True)
if p.returncode:print((p.stdout+p.stderr).decode("utf-8-sig"),flush=True)
assert p.returncode==0 and len(rs)==15
