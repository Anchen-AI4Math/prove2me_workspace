"""Split expensive upper certificate submissions under the server time limit."""
import json
import re
from pathlib import Path
from prepare_publications import write_spec, write_reference

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/'platform'

def main():
    journal=json.loads((OUT/'journal.json').read_text(encoding='utf-8'))
    foundation='namespace OAI.Snaky21\ntheorem base_valid (i : Fin 6) : Valid (baseCard i) := claim_calculus.1 i\ntheorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) : Valid (placed r t c) := claim_calculus.2.1 r t c h\nend OAI.Snaky21\n'
    helper='theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by\n  cases c\n  cases d\n  cases hA\n  cases hT\n  cases hh\n  rfl\n'
    for block in range(8,12):
        full_name=f'OAI.Snaky21.Certificate.block{block:02}_valid'
        if 'theorem:'+full_name in journal:
            raise RuntimeError('Cannot replace an already published interface: '+full_name)
        source_path=(OUT/'certificate11-computation.lean') if block==11 else (ROOT/'Solutions'/'Snaky21'/f'Certificate{block:02}.lean')
        source=source_path.read_text(encoding='utf-8')
        lo,hi=block*64,min(block*64+64,728)
        first=re.search(r'^theorem (?:calc11_|eq_)',source,re.M).start()
        starts={lo:first}
        for i in range(lo,hi):
            at=source.index(f'theorem valid_{i} :')
            starts[i+1]=source.index('\ntheorem ',at)+1
        part_names=[]
        part_size=1 if block==11 else 16
        for part,start in enumerate(range(lo,hi,part_size)):
            end=min(start+part_size,hi)
            name=f'OAI.Snaky21.Certificate.block{block:02}_part{part:02}_valid'
            part_names.append(name)
            data_module='Calc11' if block==11 else f'Data{block:02}'
            pre=f'import Definitions.Def_Snaky21{data_module}\nimport Theorems.Thm_OAI_Snaky21_claim_calculus\nimport Theorems.Thm_OAI_Snaky21_Certificate_block{block-1:02}_valid\n'
            if part:
                pre+=f'import Theorems.Thm_OAI_Snaky21_Certificate_block{block:02}_part{part-1:02}_valid\n'
            pre+='open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate\n'
            aliases=''
            for i in range(start):
                if i<lo:
                    parent=f'block{i//64:02}_valid'
                    offset=i%64
                else:
                    parent=f'block{block:02}_part{(i-lo)//part_size:02}_valid'
                    offset=(i-lo)%part_size
                aliases+=f'theorem valid_{i} : Valid card_{i} := {parent}'+'.2'*offset+'.1\n'
            typ=' ∧ '.join(f'Valid card_{i}' for i in range(start,end))+' ∧ True'
            body=source[starts[start]:starts[end]]
            code=pre+foundation+'\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace OAI.Snaky21.Certificate\n'+helper+aliases+'\n'+body+'\nend OAI.Snaky21.Certificate\n\ntheorem solution : '+typ+' :=\n  ⟨'+', '.join(f'valid_{i}' for i in range(start,end))+', True.intro⟩\n'
            slug=f'block{block:02}-part{part:02}'
            write_spec(slug,name,f'21-move certificate: validity of numbered cards {start}–{end-1}',
                       'theorem '+name+' : '+typ+' := by sorry',pre,code,
                       f'The numbered cards {start} through {end-1} of the fixed 21-move certificate are valid conditional Snaky claims, uniformly over finite prior ownership. Their literal required sets, envelopes and heights include every nested combination from the source.',
                       'Every combination equation is checked separately on its required set, envelope and height by Lean kernel computation. Placement invariance and the sound composition rule then prove validity from earlier numbered claims. This smaller group preserves the exact source data and fits the server compilation limit.',
                       f'Proposition 5 and the literal 21-move certificate, cards {start}–{end-1}.')
            write_reference(json.loads((OUT/(slug+'.json')).read_text(encoding='utf-8')))
        spec=json.loads((OUT/f'block{block:02}.json').read_text(encoding='utf-8'))
        pre=f'import Definitions.Def_Snaky21Data{block:02}\n'
        for name in part_names:
            pre+='import Theorems.Thm_'+name.replace('.','_')+'\n'
        pre+='open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate\n'
        typ=' ∧ '.join(f'Valid card_{i}' for i in range(lo,hi))+' ∧ True'
        values=[f'block{block:02}_part{(i-lo)//part_size:02}_valid'+'.2'*((i-lo)%part_size)+'.1' for i in range(lo,hi)]
        (OUT/f'block{block:02}-proof.lean').write_text(pre+'\ntheorem solution : '+typ+' :=\n  ⟨'+', '.join(values)+', True.intro⟩\n',encoding='utf-8')
        spec['preamble']=pre
        spec['explanation']='The verified smaller groups supply the numbered cards of this block. Their conjunction reconstructs the unchanged block interface. Every underlying finite equation is checked by Lean kernel reduction, and all conditional validity results are connected to earlier numbered claims and the claim calculus.'
        (OUT/f'block{block:02}.json').write_text(json.dumps(spec,indent=2,ensure_ascii=False),encoding='utf-8')
        write_reference(spec)
    print('Split upper blocks 08–11 into 36 smaller proof submissions; numbered block interfaces unchanged.')

if __name__=='__main__':
    main()
