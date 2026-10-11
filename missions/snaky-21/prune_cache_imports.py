"""Use only literal cache modules actually named by unpublished adapters."""
import hashlib
import json
import re
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/'platform'
OLD='Definitions.Def_Snaky21Calc11'

def main():
    journal=json.loads((OUT/'journal.json').read_text(encoding='utf-8'))
    cache={}
    for path in sorted((ROOT/'Definitions').glob('Def_Snaky21Calc11Part*.lean')):
        module='Definitions.'+path.stem
        for name in re.findall(r'^def (calc11_\w+)\s*:',path.read_text(encoding='utf-8'),re.M):
            if name in cache:
                raise RuntimeError('Duplicate literal cache declaration: '+name)
            cache[name]=module
    changes=[]
    for path in sorted(OUT.glob('*.json')):
        spec=json.loads(path.read_text(encoding='utf-8'))
        name=spec.get('theorem_name','')
        if not name.startswith('OAI.Snaky21.') or 'proof_file' not in spec:
            continue
        candidate=ROOT/spec['proof_file']
        code=candidate.read_text(encoding='utf-8')
        if 'import '+OLD+'\n' not in code and 'import '+OLD+'\n' not in spec['preamble']:
            continue
        proof=journal.get('proof:'+name,{})
        if proof.get('status') in ('PENDING','ACCEPTED','SKETCH_ACCEPTED'):
            raise RuntimeError('Refusing to alter a submitted adapter: '+name)
        statement=journal.get('theorem:'+name,{})
        if statement.get('status') in ('PENDING','COMPILING','PUBLISHED'):
            raise RuntimeError('Refusing to alter a published statement preamble: '+name)
        # All public types use numbered data except the finite calculation
        # batches, whose types also name their own literal outputs.
        def required_modules(text):
            return sorted({cache[token] for token in re.findall(r'\bcalc11_\w+\b',text) if token in cache})
        proof_modules=required_modules(code)
        type_modules=required_modules(spec['formal_statement'])
        def replacement(modules):
            return '\n'.join('import '+module for module in modules or ['Definitions.Def_Snaky21Data11'])+'\n'
        old_sha=hashlib.sha256(code.encode()).hexdigest()
        code=code.replace('import '+OLD+'\n',replacement(proof_modules))
        spec['preamble']=spec['preamble'].replace('import '+OLD+'\n',replacement(type_modules))
        candidate.write_text(code,encoding='utf-8')
        path.write_text(json.dumps(spec,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
        interface=ROOT/'Theorems'/('Thm_'+name.replace('.','_')+'.lean')
        interface.write_text(spec['preamble']+'\n'+spec['formal_statement']+'\n',encoding='utf-8')
        changes.append({'theorem_name':name,'proof_modules':proof_modules,'statement_modules':type_modules,
                        'old_proof_sha256':old_sha,'new_proof_sha256':hashlib.sha256(code.encode()).hexdigest()})
    (HERE/'verification'/'cache-import-pruning.json').write_text(json.dumps(changes,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print('Scoped cache imports for',len(changes),'unpublished proof adapters; actual closed proof unchanged.')

if __name__=='__main__':
    main()
