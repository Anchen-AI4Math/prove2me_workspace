"""Prepare final certificate interface and the exact existing mission reduction."""
import json
from pathlib import Path
from prepare_publications import write_spec, write_reference

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/'platform'

def main():
    catalog_type='numberedCards.length = 728 ∧ (numberedCards.map (fun c => decide (0 < c.height ∧ c.height ≤ 21))).all id = true'
    catalog_pre='import Definitions.Def_Snaky21Catalog\nopen OAI.Snaky21.Certificate\n'
    catalog_code=catalog_pre+'\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\ntheorem solution : '+catalog_type+' := by\n  decide +kernel\n\n#print axioms solution\n'
    write_spec('catalog','OAI.Snaky21.Certificate.catalog_correct','Proposition 5 — 728 numbered cards and the uniform height bound',
               'theorem OAI.Snaky21.Certificate.catalog_correct : '+catalog_type+' := by sorry',catalog_pre,catalog_code,
               'The numbered-card list for the fixed 21-move Snaky certificate has exactly 728 entries, including the six bases, and every entry has positive height at most 21. This assertion concerns the explicit finite reconstruction data only; validity as game claims is proved separately.',
               'Kernel reduction checks the literal list length and the positive height bound for every entry, including all nonbase numbered rows. This finite-data statement is separate from the game semantics and uses no external computation oracle.',
               'Proposition 5: the six bases and 722 numbered data lines, with all heights at most 21.')
    write_reference(json.loads((OUT/'catalog.json').read_text(encoding='utf-8')))
    pre='import Definitions.Def_Snaky21Data11\nimport Theorems.Thm_OAI_Snaky21_Certificate_block11_valid\nimport Theorems.Thm_OAI_Snaky21_Certificate_catalog_correct\nopen OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate\n'
    endpoint='card_727.required = ∅ ∧ card_727.height = 21 ∧ card_727.envelope.card = 251 ∧ (∀ x ∈ card_727.envelope, 0 ≤ x.1 ∧ x.1 ≤ 16 ∧ 0 ≤ x.2 ∧ x.2 ≤ 16)'
    typ='Valid card_727 ∧ ('+endpoint+') ∧ ('+catalog_type+')'
    valid='block11_valid'+'.2'*23+'.1'
    code=pre+'\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\ntheorem solution : '+typ+' := by\n  refine ⟨'+valid+', ?_, catalog_correct⟩\n  decide +kernel\n'
    write_spec('certificate','OAI.Snaky21.certificate21_correct','Proposition 5 — the valid empty-requirement card of height 21',
               'theorem OAI.Snaky21.certificate21_correct : '+typ+' := by sorry',pre,code,
               'The final numbered card 727 of the fixed 21-move certificate is a valid conditional Snaky claim, its required Maker set is empty, its height is 21, and its finite envelope has exactly 251 cells, all with both coordinates between 0 and 16. The validity is obtained from all numbered cards and their nested combinations, rather than assumed from the finite reconstruction alone.',
               'The preceding blocks reconstruct and prove the validity of every numbered card, including every nested combination, using only earlier claims and the sound conditional-claim calculus. Projecting the last block gives the validity of card 727. Independent kernel reduction of its literal finite data gives the empty required set, height 21, envelope cardinality 251, and coordinate bounds. Empty Maker and Breaker sets satisfy the final card invariant.',
               'Proposition 5, endpoint of the 21-move certificate; Lemmas 3 and 4 supply semantic validity.')
    spec=json.loads((OUT/'certificate.json').read_text(encoding='utf-8'))
    write_reference(spec)
    pre='import Definitions.Def_SnakyTwentyOne\nimport Theorems.Thm_OAI_Snaky21_certificate21_correct\nimport Theorems.Thm_OAI_Snaky21_force_extract\nopen OAI.Snaky21 OAI.SnakyPrototype OAI.SnakyPrototype.OrdinaryStrategy OAI.Snaky21.Certificate\n'
    target=json.loads((OUT/'initial.json').read_text(encoding='utf-8'))['target']
    # The target's statement closes its original namespaces. Only its type is
    # copied into the top-level solution, leaving every binder unchanged.
    signature=target['formal_statement'].split(' := by',1)[0]
    signature=signature.replace('theorem snaky_winning_strategy_21_with_legal_states','theorem solution',1)
    code=pre+'\n'+signature+' := by\n  have hc := certificate21_correct\n  have hf := hc.1.2.2 ∅ ∅ (by rw [hc.2.1.1]) (by simp)\n  rw [hc.2.1.2.1] at hf\n  exact force_extract 21 (by decide) hf\n'
    (OUT/'main-proof.lean').write_text(code,encoding='utf-8')
    explanation='The proved final certificate card has no required Maker cells and has height 21. Its conditional-claim validity therefore gives finite-horizon forcing from the empty position. The policy-extraction theorem chooses a globally fresh move from the forcing witnesses using only the remaining budget and the current ownership sets. It preserves forcing against every legal reply, continues an earlier win by fresh moves, and proves exactly 21 Maker claims and disjointness from the first 20 Breaker claims. The induction applies only before the final Maker claim; the actual 21st Breaker reply is never assumed legal. The finite certificate computations and every application of the claim calculus are supplied by the connected, verified certificate blocks.'
    spec={'theorem_id':target['theorem_id'],'theorem_name':target['theorem_name'],'proof_file':'missions/snaky-21/platform/main-proof.lean','explanation':explanation,'formal_statement':target['formal_statement']}
    (OUT/'main.json').write_text(json.dumps(spec,ensure_ascii=False,indent=2),encoding='utf-8')
    print('Prepared exact existing main-goal reduction and final certificate contribution.')

if __name__=='__main__':
    main()
