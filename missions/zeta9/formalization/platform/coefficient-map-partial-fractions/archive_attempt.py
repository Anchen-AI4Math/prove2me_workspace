from pathlib import Path
import hashlib,json,shutil
OUT=Path(__file__).resolve().parent
files=[OUT / n for n in ["prepare_batch.py","configure.py","compile-receipt.json","integration-provenance.json","definitions-request.json","problems-request.json","target-plan.json","build-0-solution.log","build-0-solution-exit.txt"]]
files+=list((OUT / "staged").rglob("*.lean"))
records=[]
for p in files:
    dst=OUT / (p.name+".before-namespace-context-fix")
    assert not dst.exists()
    shutil.copyfile(p,dst)
    records.append({"original_batch_relative":p.relative_to(OUT).as_posix(),"preserved_batch_relative":dst.name,"sha256":hashlib.sha256(dst.read_bytes()).hexdigest()})
(OUT / "retained-failed-attempt.json").write_text(json.dumps({"failure":"Appended global wrapper lacked the enclosing ZetaNine namespace resolution for relative CoefficientMapJet/CoefficientMap names in unchanged source signatures.","mathematical_source_changed":False,"remedy":"Open ZetaNine in global wrapper and problem preamble, restoring source namespace resolution; retain exact signatures and proof bodies.","files":records},indent=2)+"\n",encoding="utf-8")
