"""Publish bounded, kernel-checked numerical batches for the final row."""
import json
import re
from prepare_publications import write_spec,write_reference
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/'platform'

def main():
    source=(ROOT/'Solutions'/'Snaky21'/'Certificate11Part23.lean').read_text(encoding='utf-8')
    numerical=source[source.index('theorem calc11_'):source.index('theorem eq_card_727 :')]
    facts=list(re.finditer(r'^theorem (\w+) : (.+?) := (.*?)(?=^theorem |\Z)',numerical,re.M|re.S))
    assert len(facts)==130,len(facts)
    pre='import Definitions.Def_Snaky21Calc11\nopen OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate\n'
    helper='theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by\n  cases c\n  cases d\n  cases hA\n  cases hT\n  cases hh\n  rfl\n'
    imports=[]
    aliases=[]
    for part,start in enumerate(range(0,len(facts),16)):
        selected=facts[start:start+16]
        name=f'OAI.Snaky21.Certificate.final_calculations_part{part:02}_correct'
        local_name=name.rsplit('.',1)[1]
        imports.append('import Theorems.Thm_'+name.replace('.','_')+'\n')
        typ=' ∧ '.join('('+f.group(2)+')' for f in selected)+' ∧ True'
        bodies='\n'.join(f.group(0).rstrip() for f in selected)
        values=', '.join(f.group(1) for f in selected)
        code=pre+'\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace OAI.Snaky21.Certificate\n'+helper+'\n'+bodies+'\nend OAI.Snaky21.Certificate\n\ntheorem solution : '+typ+' :=\n  ⟨'+values+', True.intro⟩\n'
        slug=f'final-calculations{part:02}'
        write_spec(slug,name,f'Final Snaky certificate: finite calculations {start}–{start+len(selected)-1}',
                   'theorem '+name+' : '+typ+' := by sorry',pre,code,
                   'The fixed placements and finite-set operations in this batch equal their literal integer-grid outputs. These equalities supply the required sets, envelopes, and heights in the final 32-child certificate composition.',
                   'Each equality is checked by Lean kernel reduction. Card equalities are checked separately on their required set, envelope and height, then combined by record extensionality. The batches bound compilation resources while preserving all operands and outputs of the pinned certificate.',
                   'Proposition 5 and the last certificate row (numbered card 727).')
        write_reference(json.loads((OUT/(slug+'.json')).read_text(encoding='utf-8')))
        for offset,f in enumerate(selected):
            aliases.append(f'theorem {f.group(1)} : {f.group(2)} := {local_name}'+'.2'*offset+'.1\n')
    path=OUT/'block11-part23-proof.lean'
    text=path.read_text(encoding='utf-8')
    start=text.index('theorem calc11_')
    end=text.index('theorem eq_card_727 :',start)
    text=''.join(imports)+text[:start]+'\n'.join(aliases)+'\n'+text[end:]
    path.write_text(text,encoding='utf-8')
    spec=json.loads((OUT/'block11-part23.json').read_text(encoding='utf-8'))
    spec['preamble']=''.join(imports)+spec['preamble']
    spec['explanation']='The verified finite-calculation batches establish the 32 placements and all required/envelope unions, common intersections and final erase/insert operations. Explicit congruence composes these equalities into the last card equation; the sound conditional-claim composition rule proves validity from the earlier numbered cards.'
    (OUT/'block11-part23.json').write_text(json.dumps(spec,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    write_reference(spec)
    print('Prepared nine bounded numerical batches and connected them to final card 727.')

if __name__=='__main__':
    main()
