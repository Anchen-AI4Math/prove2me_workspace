"""Source fingerprints for supplementary Lean-parsed scope/header context.

Official Stage 1 and Stage 2 remain the only declaration/proof/reference
oracles. Supplementary syntax is used for non-declaration scope commands,
import headers and declaration attributes, and must agree with Stage 2 spans.
"""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
plan=json.loads((VER/'machine-upload-plan.json').read_text(encoding='utf-8'))
inputs=[]
for module in plan['participating_modules']:
    path=HERE/'machine/lean'/Path(*module.split('.')).with_suffix('.lean')
    inputs.append({'module':module,'path':path.as_posix(),
                   'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                   'oracle_input_sha256':hashlib.sha256(path.read_text(encoding='utf-8').encode()).hexdigest()})
(VER/'machine-context-inputs.json').write_text(json.dumps(inputs,indent=2)+'\n',encoding='utf-8')
print('Prepared',len(inputs),'immutable context source fingerprints.')
