"""Blank only official Stage 2 declaration spans for a context-only parser.

The supplementary parser reads namespace/section/end commands. Declaration
spans, proof cuts and identifier references still come only from official
Stage 1 / Stage 2 facts. Blanking preserves byte offsets and newlines.
"""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
OUT=VER/'model-context-inputs'
OUT.mkdir(exist_ok=True)
plan=json.loads((VER/'model-upload-plan.json').read_text(encoding='utf-8'))
inputs=[]
for module in plan['participating_modules']:
    stem=module.replace('.','_')
    source=HERE/'machine/lean'/Path(*module.split('.')).with_suffix('.lean')
    raw_data=source.read_bytes()
    # Lean IO.FS.readFile normalizes Windows CRLF to LF before reporting its
    # UTF-8 byte offsets. Apply edits to those same normalized bytes, while
    # retaining the raw-file hash as the immutable provenance check.
    data=source.read_text(encoding='utf-8').encode('utf-8')
    receipt=json.loads((VER/'model-sketch-oracles'/(stem+'.receipt.json')).read_text(encoding='utf-8'))
    assert receipt['exit_code']==0
    assert hashlib.sha256(raw_data).hexdigest()==receipt['source_sha256']
    facts=[json.loads(line) for line in (VER/'model-sketch-oracles'/(stem+'.jsonl'))
           .read_text(encoding='utf-8').splitlines() if line.strip()]
    blank=bytearray(data)
    for fact in facts:
        if fact['kind']!='decl':continue
        for index in range(fact['declStart']['offset'],fact['declEnd']['offset']):
            if blank[index] not in (10,13):blank[index]=32
    target=OUT/(stem+'.lean')
    target.write_bytes(blank)
    inputs.append({'module':module,'path':target.relative_to(ROOT).as_posix()})
(VER/'model-context-inputs.json').write_text(json.dumps(inputs,indent=2)+'\n',encoding='utf-8')
print('Prepared',len(inputs),'context-only skeletons from official declaration spans.')
