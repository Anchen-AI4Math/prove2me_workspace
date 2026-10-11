"""Clarify public title only; preserve every formal statement, preamble and staged proof byte."""
from pathlib import Path
import json,hashlib
OUT=Path(__file__).resolve().parent
p=OUT / "problems-request.json"
old=p.read_bytes();r=json.loads(old)
assert r["problems"][0]["theorem_name"]=="ZetaNine.CoefficientMapReflection.local_coefficient_reflection"
previous=r["problems"][0]["theorem_title"]
title="Actual local coefficient reflection at every pole for even n"
r["problems"][0]["theorem_title"]=title
p.write_text(json.dumps(r,ensure_ascii=False,indent=2)+"\n",encoding="utf-8",newline="\n")
# Make the source recipe reproduce this clearer title as well.
for name in ["configure.py","prepare_batch.py"]:
    f=OUT / name;s=f.read_text(encoding="utf-8-sig")
    assert previous in s or title in s
    f.write_text(s.replace(previous,title),encoding="utf-8",newline="\n")
(OUT / "request-title-provenance.json").write_text(json.dumps({"field":"problems[0].theorem_title","previous_title":previous,"final_title":title,"reason":"n is the even parameter; genuine pole order is9. The title should not call n the pole order.","formal_statements_or_preambles_or_proof_sources_changed":False,"before_request_sha256":hashlib.sha256(old).hexdigest(),"after_request_sha256":hashlib.sha256(p.read_bytes()).hexdigest()},indent=2)+"\n",encoding="utf-8")
print("Public title clarified; formal bytes preserved.")
