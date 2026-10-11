"""Prepare exact platform interfaces and self-contained proof adapters."""
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/'platform'
PAPER='https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf'

def without_imports(code):
    return '\n'.join(line for line in code.splitlines() if not line.startswith('import '))+'\n'

def write_spec(slug,name,title,formal,preamble,code,description,explanation,source):
    proof=OUT/(slug+'-proof.lean')
    proof.write_text(code,encoding='utf-8')
    spec={'theorem_name':name,'theorem_title':title,'formal_statement':formal,
          'preamble':preamble,'natural_language_statement':description,'source':PAPER+'; '+source,
          'proof_file':proof.relative_to(ROOT).as_posix(),'explanation':explanation}
    (OUT/(slug+'.json')).write_text(json.dumps(spec,indent=2,ensure_ascii=False),encoding='utf-8')

def write_reference(spec):
    name=spec['theorem_name'].replace('.','_')
    path=ROOT/'Theorems'/('Thm_'+name+'.lean')
    path.write_text('-- Exact public interface; reference placeholder, not proof evidence.\n'+spec['preamble']+'\n'+spec['formal_statement']+'\n',encoding='utf-8')

def main():
    OUT.mkdir(exist_ok=True)
    forcing=(ROOT/'Solutions'/'Snaky21'/'Forcing.lean').read_text(encoding='utf-8')
    geometry=(ROOT/'Solutions'/'Snaky21'/'Geometry.lean').read_text(encoding='utf-8')
    strategy=(ROOT/'Solutions'/'Snaky21'/'Strategy.lean').read_text(encoding='utf-8')
    existing=json.loads((OUT/'combination.json').read_text(encoding='utf-8'))
    write_reference(existing)
    cut=forcing[:forcing.index('theorem combination_rule')]+forcing[forcing.index('theorem base_valid'):]
    pre='import Definitions.Def_Snaky21Core\nimport Theorems.Thm_OAI_Snaky21_combination_rule\nopen OAI.Snaky21 OAI.SnakyPrototype\n'
    typ='(∀ i : Fin 6, Valid (baseCard i)) ∧ (∀ (r : Fin 8) (t : Cell) (c : Card), Valid c → Valid (placed r t c)) ∧ (∀ (p : Cell) (cs : List Card), cs ≠ [] → (∀ c ∈ cs, Valid c) → Valid (combine p cs))'
    code=pre+without_imports(cut)+without_imports(geometry)+'\ntheorem solution : '+typ+' :=\n  ⟨base_valid, fun r t c hc => placed_valid r t hc, combination_rule⟩\n'
    write_spec('calculus','OAI.Snaky21.claim_calculus','Conditional Snaky claim calculus: bases, placements, and composition',
               'theorem OAI.Snaky21.claim_calculus : '+typ+' := by sorry',pre,code,
               'The six one-cell completions of Snaky are valid conditional claims. Every translated, rotated or reflected valid claim remains valid with the same height. The nonempty composition rule of Lemma 3 preserves validity, counting a fresh replacement for an already-owned pivot as one actual Maker claim. Validity is uniform over finite prior ownership with the required Maker cells present and Breaker avoiding the envelope.',
               'The bases either have an already completed target or a free missing cell. The eight orientations form a group of bijections; transporting both ownership sets and moves preserves legality and transports every Snaky target. For arbitrary initial ownership, preimages under the placement recover the original conditional claim. The composition component uses the already verified Lemma 3.',
               'Definition 2, Lemmas 3 and 4, and the placement invariance immediately following Definition 2.')
    partial=forcing[:forcing.index('theorem canForce_step')]+'\nend OAI.Snaky21\n'
    signature=strategy[strategy.index('theorem force_extract'):strategy.index(' := by',strategy.index('theorem force_extract'))]
    pre='import Definitions.Def_Snaky21Core\nopen OAI.Snaky21 OAI.SnakyPrototype OAI.SnakyPrototype.OrdinaryStrategy\n'
    code=pre+without_imports(partial)+without_imports(strategy)+'\n'+signature.replace('theorem force_extract','theorem solution',1)+' :=\n  force_extract N hN hstart\n\n#print axioms solution\n'
    write_spec('strategy','OAI.Snaky21.force_extract','A legal positional policy extracted from finite-horizon forcing',
               signature.replace('theorem force_extract','theorem OAI.Snaky21.force_extract',1)+' := by sorry',pre,code,
               'For a positive number N, suppose Maker can force a Snaky target within N further actual claims from the empty board, in the finite-horizon forcing relation. There exists one policy depending only on the remaining budget and the two current ownership sets, legal on every finite input. Against every reply sequence legal before the final round, Maker has a target and exactly N cells after its Nth claim, disjoint from the first N−1 Breaker cells. Before that final claim both ownership sets are disjoint and Breaker has made exactly the recorded number of claims. No Nth Breaker reply is assumed legal.',
               'At each state and remaining budget the policy selects a witness to the forcing relation, using classical choice. Where no witness exists it selects a cell whose first coordinate exceeds the absolute first coordinates of all owned cells. This makes it globally legal. Induction on the played rounds preserves the forcing relation; an earlier target persists under fresh continuation. At the last round a hypothetical fresh reply suffices to recover the target from the zero-budget relation, so the actual final reply is irrelevant. Separate insertion inductions prove the exact cardinalities and disjointness.',
               'The main theorem strategy argument and its fixed-endpoint reformulation; build/strategy.tex, section One strategy against every continuation.')
    for slug in ('calculus','strategy'):
        write_reference(json.loads((OUT/(slug+'.json')).read_text(encoding='utf-8')))

    base_aliases='namespace OAI.Snaky21\ntheorem base_valid (i : Fin 6) : Valid (baseCard i) := claim_calculus.1 i\ntheorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) : Valid (placed r t c) := claim_calculus.2.1 r t c h\nend OAI.Snaky21\n'
    helper='namespace OAI.Snaky21.Certificate\ntheorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by\n  cases c\n  cases d\n  cases hA\n  cases hT\n  cases hh\n  rfl\nend OAI.Snaky21.Certificate\n'
    for block in range(12):
        path=ROOT/'Solutions'/'Snaky21'/f'Certificate{block:02}.lean'
        source=path.read_text(encoding='utf-8')
        lo,hi=block*64,min((block+1)*64,728)
        typ=' ∧ '.join(f'Valid card_{i}' for i in range(lo,hi))+' ∧ True'
        pre=f'import Definitions.Def_Snaky21Data{block:02}\nimport Theorems.Thm_OAI_Snaky21_claim_calculus\n'
        if block:
            pre+=f'import Theorems.Thm_OAI_Snaky21_Certificate_block{block-1:02}_valid\n'
        pre+='open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate\n'
        aliases='namespace OAI.Snaky21.Certificate\n'
        for i in range(lo):
            parent=i//64
            projection='.2'*(i%64)+'.1'
            aliases+=f'theorem valid_{i} : Valid card_{i} := block{parent:02}_valid{projection}\n'
        aliases+='end OAI.Snaky21.Certificate\n'
        code=pre+base_aliases+(helper if block else '')+aliases+without_imports(source)+f'\ntheorem solution : {typ} := block{block:02}_valid\n'
        name=f'OAI.Snaky21.Certificate.block{block:02}_valid'
        write_spec(f'block{block:02}',name,f'21-move certificate: validity of numbered cards {lo}–{hi-1}',
                   f'theorem {name} : {typ} := by sorry',pre,code,
                   f'Every numbered card from {lo} through {hi-1} of the fixed 21-move certificate is a valid conditional claim. The required set, envelope and height are the literal finite reconstruction of the printed data, including every nested combination. Every actual combination equation is checked by Lean kernel reduction, and the game meaning follows from the conditional-claim calculus and earlier numbered cards.',
                   'Each placed reference preserves validity. Every nested and numbered combination is reconstructed independently from the literal required sets, envelopes and heights; its three field equations are proved by kernel computation. Applying Lemma 3 then proves the corresponding conditional claim. Only earlier numbered claims are used. The final conjunction packages all numbered claims in this block for the next block.',
                   'Proposition 5, 21-move certificate appendix, numbered cards '+str(lo)+'–'+str(hi-1)+'.')
        write_reference(json.loads((OUT/f'block{block:02}.json').read_text(encoding='utf-8')))
    scope_path=HERE/'scope.json'
    scope=json.loads(scope_path.read_text(encoding='utf-8'))
    pattern='Theorems/Thm_OAI_Snaky21*.lean'
    if pattern not in scope['sources']:
        scope['sources'].append(pattern)
    scope_path.write_text(json.dumps(scope,indent=2)+'\n',encoding='utf-8')
    print('Prepared reusable calculus, policy extraction, and 12 dependency-connected certificate block interfaces.')

if __name__=='__main__':
    main()
