from pathlib import Path
import hashlib,json,traceback
OUT=Path(__file__).resolve().parent
p=OUT / "audit_and_freeze.py"
g={"__file__":str(p),"__name__":"__main__"}
try:exec(compile(p.read_bytes(),str(p),"exec"),g)
except AssertionError as e:
    keep=OUT / "audit_and_freeze.py.before-splice-oracle-fix"
    if not keep.exists():keep.write_bytes(p.read_bytes())
    actual=(OUT / "staged" / g["t"]["local_solution"]).read_bytes();expected=g["reconstructed"].encode()
    index=next((i for i,(a,b) in enumerate(zip(actual,expected)) if a!=b),min(len(actual),len(expected)))
    d={"verdict":"FAIL","phase":"author Python exact source splice gate","error":str(e),"traceback":traceback.format_exc(),"checks":g["checks"],"actual_proof_source_modified":False,"native_and_staged_Lean_compilations_exit_zero":True,"first_difference_offset":index,"actual_context":actual[max(0,index-100):index+180].decode(),"oracle_reconstruction_context":expected[max(0,index-100):index+180].decode(),"actual_bytes":len(actual),"reconstructed_bytes":len(expected),"stage_replays":g["stage_replays"],"original_audit_script_sha256":hashlib.sha256(p.read_bytes()).hexdigest()}
    (OUT / "audit-gate-failed-attempt.json").write_text(json.dumps(d,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:d[k] for k in ["first_difference_offset","actual_context","oracle_reconstruction_context","actual_bytes","reconstructed_bytes","stage_replays"]},ensure_ascii=False))
