"""Keep statements lightweight and make proof imports explicit before queuing."""
import json
import re
from pathlib import Path
from prepare_publications import write_reference
import publish

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/'platform'

def main():
    journal=publish.read_journal()
    changed=[]
    for path in sorted(OUT.glob('*.json')):
        spec=json.loads(path.read_text(encoding='utf-8'))
        name=spec.get('theorem_name','')
        if not name.startswith('OAI.Snaky21.') or 'proof_file' not in spec:
            continue
        proof=journal.get('proof:'+name,{})
        if proof.get('status') in ('ACCEPTED','PENDING','SKETCH_ACCEPTED'):
            continue
        candidate=ROOT/spec['proof_file']
        code=candidate.read_text(encoding='utf-8')
        # A minimal statement module reexports only definitions. Consequently
        # any projection used by an adapter must have its own explicit import.
        parents=set(re.findall(r'(?::=\s+|\b)(block\d+(?:_part\d+)?(?:_group\d+)?_valid)\b',code))
        imports=set(re.findall(r'^import\s+(\S+)',code,re.M))
        extra=[]
        for parent in sorted(parents):
            module='Theorems.Thm_OAI_Snaky21_Certificate_'+parent
            if module not in imports:
                extra.append('import '+module)
        if extra:
            candidate.write_text('\n'.join(extra)+'\n'+code,encoding='utf-8')
        # Previously published statements are immutable. For new statements,
        # theorem imports are unnecessary for these concrete data predicates.
        if 'theorem:'+name not in journal:
            lines=spec['preamble'].splitlines()
            pre=[line for line in lines if not line.startswith('import Theorems.')]
            if 'numberedCards' in spec['formal_statement'] and 'import Definitions.Def_Snaky21Catalog' not in pre:
                pre.insert(0,'import Definitions.Def_Snaky21Catalog')
            if not any(line.startswith('import Definitions.') for line in pre):
                pre.insert(0,'import Definitions.Def_Snaky21Core')
            spec['preamble']='\n'.join(pre)+'\n'
            path.write_text(json.dumps(spec,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
            write_reference(spec)
        changed.append(path.name)
    (HERE/'verification'/'queue-adapters.json').write_text(json.dumps(changed,indent=2)+'\n',encoding='utf-8')
    print('Prepared',len(changed),'remaining adapters; no accepted or pending proof changed.')

if __name__=='__main__':
    main()
