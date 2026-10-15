"""Inventory changed 256/512 literals for semantic review; not declaration extraction."""
from pathlib import Path
import re
root=Path(__file__).resolve().parent
src=root/'verification/upstream'
for p in sorted((root/'machine/lean/Submission').rglob('*.lean')):
    old=src/p.relative_to(root/'machine/lean')
    if not old.exists(): continue
    original=old.read_text(encoding='utf-8-sig')
    port=p.read_text(encoding='utf-8')
    if not re.search(r'\b(?:256|512)\b',original): continue
    if original==port: continue
    for i,line in enumerate(original.splitlines(),1):
        if re.search(r'\b(?:256|512)\b',line):
            print(p.relative_to(root/'machine/lean').as_posix(),i,line.strip())
