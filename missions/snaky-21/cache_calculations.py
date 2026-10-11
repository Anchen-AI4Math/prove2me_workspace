"""Factor kernel checks into bounded finite-set operations (untrusted generator)."""
import re
from pathlib import Path
from generate_certificate import load_module, finite, card, cell, SYMMETRY

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]

def main():
    ind=load_module('snaky_cached_evaluator',HERE/'source'/'verification'/'supporting'/'independent_evaluator.py')
    cert=ind.Certificate((HERE/'source'/'verification'/'certificate.txt').read_text(encoding='ascii'))
    data=[]
    proofs={}
    counter=0
    inline=0

    def literal_set(points):
        nonlocal counter
        name=f'calc11_set_{counter}'
        counter+=1
        data.append(f'def {name} : Finset OAI.SnakyPrototype.Cell := {finite(points)}\n')
        return name

    def op(kind,left,left_value,right,right_value,lines):
        result=left_value|right_value if kind=='∪' else left_value&right_value
        target=literal_set(result)
        lemma=f'{target}_eq'
        lines.append(f'theorem {lemma} : {left} {kind} {right} = {target} := by decide +kernel\n')
        return target,result,lemma

    def encode(tree,parent,active):
        nonlocal counter,inline
        if isinstance(tree,ind.Reference):
            value=ind.transform(cert.cards[tree.card],tree.symmetry,tree.shift)
            term=f'placed {SYMMETRY[tree.symmetry]} {cell(tree.shift)} card_{tree.card}'
            return term,value,None
        children=[encode(c,None,active) for c in tree.children]
        name=parent
        if name is None:
            name=f'inline_{inline}'
            inline+=1
        value=cert.evaluate(tree)
        if not active:
            return name,value,None
        lines=[]
        cached=[]
        ref_lemmas=[]
        for term,val,_ in children:
            if term.startswith('placed '):
                cached_name=f'calc11_card_{counter}'
                counter+=1
                data.append(f'def {cached_name} : OAI.Snaky21.Card := {card(val)}\n')
                lemma=cached_name+'_eq'
                lines.append(f'theorem {lemma} : {term} = {cached_name} := by\n  apply computed_card_ext <;> decide +kernel\n')
                ref_lemmas.append(lemma)
                cached.append((cached_name,val))
            else:
                cached.append((term,val))
        A,Aval='∅',frozenset()
        T,Tval='∅',frozenset()
        Aeq,Teq=[],[]
        for term,val in reversed(cached):
            A,Aval,lemma=op('∪',term+'.required',val.required,A,Aval,lines)
            Aeq.append(lemma)
            T,Tval,lemma=op('∪',term+'.envelope',val.support,T,Tval,lines)
            Teq.append(lemma)
        I,Ival=cached[0][0]+'.envelope',cached[0][1].support
        Ieq=[]
        for term,val in reversed(cached[1:]):
            I,Ival,lemma=op('∩',term+'.envelope',val.support,I,Ival,lines)
            Ieq.append(lemma)
        U,Uval,Ueq=op('∪',A,Aval,I,Ival,lines)
        erase=f'calc11_finishA_{counter}'
        insert=f'calc11_finishT_{counter}'
        counter+=1
        lines.append(f'theorem {erase} : {U}.erase {cell(tree.pivot)} = {name}.required := by decide +kernel\n')
        lines.append(f'theorem {insert} : insert {cell(tree.pivot)} {T} = {name}.envelope := by decide +kernel\n')
        expr=f'combine {cell(tree.pivot)} ['+', '.join(term for term,_,_ in children)+']'
        eq=f'theorem eq_{name} : {name} = {expr} := by\n'
        if ref_lemmas:
            eq+='  rw ['+', '.join(ref_lemmas)+']\n'
        eq+='  apply computed_card_ext\n'
        eq+='  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]\n'
        eq+='    rw ['+', '.join(Aeq+Ieq+[Ueq,erase])+']\n'
        eq+='  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]\n'
        eq+='    rw ['+', '.join(Teq+[insert])+']\n'
        eq+='  · decide +kernel\n'
        proofs[name]='\n'.join(lines)+'\n'+eq
        return name,value,None

    for i in range(6,728):
        encode(cert.expressions[i],f'card_{i}',i>=704)
    path=ROOT/'Definitions'/'Def_Snaky21Calc11.lean'
    text='import Definitions.Def_Snaky21Data11\n\nnamespace OAI.Snaky21.Certificate\n\n'+'\n'.join(data)+'\nend OAI.Snaky21.Certificate\n'
    path.write_text(text,encoding='utf-8')
    source_path=ROOT/'Solutions'/'Snaky21'/'Certificate11.lean'
    original=source_path.read_text(encoding='utf-8')
    original=re.sub(r'theorem eq_(card_\d+|inline_\d+) : .*?\n  apply computed_card_ext <;> decide \+kernel\n',lambda m:proofs[m.group(1)],original,flags=re.S)
    original=original.replace('import Definitions.Def_Snaky21Data11','import Definitions.Def_Snaky21Calc11',1)
    source_path.write_text(original,encoding='utf-8')
    print(f'Factored block 11 into {counter} bounded cache values; {len(proofs)} combination identities remain kernel-checked.')

if __name__=='__main__':
    main()
