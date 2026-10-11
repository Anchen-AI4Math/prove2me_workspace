"""Keep published interfaces fixed while subdividing unaccepted heavy proofs."""
import json
import re
from pathlib import Path
from prepare_publications import write_spec, write_reference

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/'platform'

def main():
    journal=json.loads((OUT/'journal.json').read_text(encoding='utf-8'))
    for block in (9,10):
        for part in range(4):
            slug=f'block{block:02}-part{part:02}'
            spec_path=OUT/(slug+'.json')
            spec=json.loads(spec_path.read_text(encoding='utf-8'))
            record=journal.get('proof:'+spec['theorem_name'],{})
            if record.get('status') in ('PENDING','ACCEPTED','SKETCH_ACCEPTED'):
                continue
            if list(OUT.glob(slug+'-group*.json')):
                continue
            code=(OUT/(slug+'-proof.lean')).read_text(encoding='utf-8')
            lo=block*64+part*16
            hi=lo+16
            first=re.search(r'^theorem eq_',code,re.M).start()
            prefix=code[:first]
            starts={lo:first}
            for i in range(lo,hi-1):
                at=code.index(f'theorem valid_{i} :')
                starts[i+1]=code.index('\ntheorem ',at)+1
            starts[hi]=code.rindex('\nend OAI.Snaky21.Certificate')
            groups=[]
            for group,start in enumerate(range(lo,hi,4)):
                name=spec['theorem_name'].replace('_valid',f'_group{group:02}_valid')
                groups.append(name)
                extra=''
                if group:
                    extra='import Theorems.Thm_'+groups[group-1].replace('.','_')+'\n'
                aliases=''
                for i in range(lo,start):
                    parent=f'block{block:02}_part{part:02}_group{(i-lo)//4:02}_valid'
                    aliases+=f'theorem valid_{i} : Valid card_{i} := '+parent+'.2'*((i-lo)%4)+'.1\n'
                typ=' ∧ '.join(f'Valid card_{i}' for i in range(start,start+4))+' ∧ True'
                body=code[starts[start]:starts[start+4]]
                payload=extra+prefix+aliases+'\n'+body+'\nend OAI.Snaky21.Certificate\n\ntheorem solution : '+typ+' :=\n  ⟨'+', '.join(f'valid_{i}' for i in range(start,start+4))+', True.intro⟩\n'
                child_slug=slug+f'-group{group:02}'
                pre=extra+spec['preamble']
                write_spec(child_slug,name,f'21-move certificate: validity of numbered cards {start}–{start+3}',
                    'theorem '+name+' : '+typ+' := by sorry',pre,payload,
                    f'The four numbered conditional Snaky claims {start} through {start+3} of the pinned certificate are valid, including the nested combinations in their definitions.',
                    'Kernel reduction verifies each required set, envelope, and height. The proved placement and combination calculus gives semantic validity from earlier numbered claims. Four-card groups keep the unchanged published parent statement within the server compiler deadline.',
                    f'Proposition 5, certificate cards {start}–{start+3}.')
                write_reference(json.loads((OUT/(child_slug+'.json')).read_text(encoding='utf-8')))
            pre=spec['preamble']
            pre=''.join('import Theorems.Thm_'+name.replace('.','_')+'\n' for name in groups)+pre
            typ=spec['formal_statement'].split(' : ',1)[1].split(' := by',1)[0]
            values=[f'block{block:02}_part{part:02}_group{(i-lo)//4:02}_valid'+'.2'*((i-lo)%4)+'.1' for i in range(lo,hi)]
            (OUT/(slug+'-proof.lean')).write_text(pre+'\ntheorem solution : '+typ+' :=\n  ⟨'+', '.join(values)+', True.intro⟩\n',encoding='utf-8')
            spec['preamble']=pre
            spec['explanation']='The four-card subgroups verify the literal finite equations and conditional game claims. Their conjunction proves this unchanged sixteen-card parent interface, with every child connected to the earlier certificate chain.'
            spec_path.write_text(json.dumps(spec,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
            write_reference(spec)
            print('Subdivided',slug,flush=True)

if __name__=='__main__':
    main()
