"""Relocate exact literal cache definitions into two-numbered-card modules."""
import hashlib
import json
import re
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/'Definitions'/'Def_Snaky21Calc11.lean'
BACKUP=HERE/'platform'/'calc11-original-definition.lean'

def main():
    original=SOURCE.read_bytes()
    if not BACKUP.exists():
        BACKUP.write_bytes(original)
    text=BACKUP.read_text(encoding='utf-8')
    declarations=dict(re.findall(r'^(def (calc11_(?:card|set)_\d+) : [^\n]+)\n',text,re.M)[i][::-1] for i in range(len(re.findall(r'^def calc11_',text,re.M))))
    # Every cache definition is a literal: no dependency on another cache.
    for name,decl in declarations.items():
        if set(re.findall(r'calc11_(?:card|set)_\d+',decl))!={name}:
            raise RuntimeError('A cache is not a literal: '+name)
    assigned={}
    for part in range(24):
        proof=(ROOT/'Solutions'/'Snaky21'/f'Certificate11Part{part:02}.lean').read_text(encoding='utf-8')
        refs=set(re.findall(r'\bcalc11_(?:card|set)_\d+\b',proof))&declarations.keys()
        for name in refs:
            if name in assigned and assigned[name]!=part//2:
                raise RuntimeError('Cache shared across numbered-card groups: '+name)
            assigned[name]=part//2
    if set(assigned)!=set(declarations):
        raise RuntimeError('An original cache is not assigned')
    modules=[]
    sizes=[]
    reconstructed=[]
    for group in range(12):
        module=f'Definitions.Def_Snaky21Calc11Part{group:02}'
        modules.append(module)
        pieces=[decl for name,decl in declarations.items() if assigned[name]==group]
        reconstructed.extend(pieces)
        dependency='Definitions.Def_Snaky21Data11' if group==0 else f'Definitions.Def_Snaky21Calc11Part{group-1:02}'
        payload='import '+dependency+'\n\nnamespace OAI.Snaky21.Certificate\n\n'+'\n\n'.join(pieces)+'\n\nend OAI.Snaky21.Certificate\n'
        path=ROOT/'Definitions'/f'Def_Snaky21Calc11Part{group:02}.lean'
        path.write_text(payload,encoding='utf-8')
        sizes.append({'file':str(path.relative_to(ROOT)),'numbered_cards':[704+2*group,705+2*group],'literal_definitions':len(pieces),'bytes':len(payload.encode())})
    if reconstructed!=list(declarations.values()):
        raise RuntimeError('The literal order or contents changed')
    SOURCE.write_text('-- Exact original literal caches, split by pairs of numbered rows.\n'+'\n'.join('import '+module for module in modules)+'\n',encoding='utf-8')
    scope_path=HERE/'scope.json'
    scope=json.loads(scope_path.read_text(encoding='utf-8'))
    pattern='Definitions/Def_Snaky21Calc11Part*.lean'
    if pattern not in scope['sources']:
        scope['sources'].append(pattern)
    scope_path.write_text(json.dumps(scope,indent=2)+'\n',encoding='utf-8')
    report={'original_sha256':hashlib.sha256(BACKUP.read_bytes()).hexdigest(),'literal_definitions':len(declarations),'all_original_declarations_identical_and_ordered':True,'parts':sizes}
    (HERE/'verification'/'cache-split.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
