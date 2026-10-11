"""Connect the existing mission through a faithful, locally closed forcing lemma."""
import json
import sys
from pathlib import Path
import pipeline
import publish
from prepare_publications import write_spec, write_reference

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = HERE/'platform'
NAME = 'OAI.Snaky21.empty_position_force21'

def prepare():
    pre = 'import Theorems.Thm_OAI_Snaky21_certificate21_correct\nopen OAI.Snaky21 OAI.SnakyPrototype\n'
    code = pre + '''
theorem solution : CanForce 21 ∅ ∅ := by
  have hc := certificate21_correct
  have hf := hc.1.2.2 ∅ ∅ (by rw [hc.2.1.1]) (by simp)
  rw [hc.2.1.2.1] at hf
  exact hf
'''
    # The statement needs only the public game/forcing definitions. Its proof
    # will connect the finite certificate after that certificate is published.
    statement_pre = 'import Definitions.Def_Snaky21Core\nopen OAI.Snaky21 OAI.SnakyPrototype\n'
    write_spec('empty-force', NAME, 'Proposition 5 — forcing Snaky from the empty position in 21 Maker claims',
        'theorem '+NAME+' : CanForce 21 ∅ ∅ := by sorry', statement_pre, code,
        'On the infinite integer board, Maker can force Snaky from the empty position with a budget of 21 actual further Maker claims. The recursive forcing predicate quantifies over every legal Breaker response and permits an immediate win. This is the semantic consequence of the empty-requirement, height-21 certificate card in Proposition 5.',
        'Apply the final card validity to empty Maker and Breaker sets. Its required set is empty and its height equals 21. This isolates finite-position forcing from the separate extraction of a globally legal policy and exact play counts.',
        'Proposition 5 and the terminal conditional claim of the pinned 21-move certificate.')
    spec = json.loads((OUT/'empty-force.json').read_text(encoding='utf-8'))
    write_reference(spec)
    check = OUT/'empty-force-local-check.lean'
    check.write_text('import Solutions.Snaky21.Main\nopen OAI.Snaky21 OAI.SnakyPrototype\n'
                     'theorem checked : CanForce 21 ∅ ∅ := certificate21_force\n#print axioms checked\n', encoding='utf-8')
    main_spec = json.loads((OUT/'main.json').read_text(encoding='utf-8'))
    original = main_spec['formal_statement'].split(' := by', 1)[0]
    signature = original.replace('theorem snaky_winning_strategy_21_with_legal_states', 'theorem solution', 1)
    main = '''import Definitions.Def_SnakyTwentyOne
import Theorems.Thm_OAI_Snaky21_empty_position_force21
import Theorems.Thm_OAI_Snaky21_force_extract
open OAI.Snaky21 OAI.SnakyPrototype OAI.SnakyPrototype.OrdinaryStrategy

''' + signature + ' := by\n  exact force_extract 21 (by decide) empty_position_force21\n'
    (OUT/'main-proof.lean').write_text(main, encoding='utf-8')
    main_spec['explanation'] = (
        'This reduction separates the paper\'s finite-position certificate from policy extraction. '
        'The child empty_position_force21 supplies forcing from the empty board with a budget of 21 actual Maker claims. '
        'The proved general force_extract theorem constructs a policy depending only on the remaining budget and current ownership sets, '
        'with a fresh fallback on arbitrary inputs and after an early win. It proves exactly 21 Maker claims, all required disjointness '
        'and Breaker counts, assuming legality of only the first 20 Breaker replies. '
        'At initial submission the certificate child remains Open on the platform, so this is a reduction sketch, not a completed mission. '
        'The corresponding actual closed Lean proof has already passed local kernel and axiom checks; its finite certificate dependencies are being published sequentially.')
    (OUT/'main.json').write_text(json.dumps(main_spec, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    return spec, main_spec, check

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    spec, main_spec, check = prepare()
    pipeline.run_checked([str(pipeline.LEAN), '-DautoImplicit=false', str(check)], 'empty-force-closed-check')
    target = 'Theorems.Thm_'+NAME.replace('.', '_')
    pipeline.build_interface(target, 'empty-force-interface')
    candidate = ROOT/main_spec['proof_file']
    pipeline.run_checked([str(pipeline.LEAN), '-DautoImplicit=false', str(candidate)], 'main-sketch-local')
    token = publish.api.get_token()
    journal = publish.read_journal()
    key = 'theorem:'+NAME
    if key not in journal:
        publish.ensure_available(NAME, token)
        data = {k:spec[k] for k in ['theorem_name','theorem_title','formal_statement','natural_language_statement','preamble','source']}
        data['env'] = publish.ENV
        result = publish.request('POST', '/submit-problem', token, data)
        journal[key] = {'job_id':result['jobs'][0]['job_id'], 'spec':str((OUT/'empty-force.json').relative_to(ROOT)), 'job_history':[]}
        publish.save_journal(journal)
    publish.wait_job(journal, key, token)
    publish.submit(main_spec['theorem_id'], candidate, main_spec['explanation'], token, journal, main_spec['theorem_name'])
    graph = publish.request('GET', '/theorems/'+main_spec['theorem_id']+'/graph', publish.api.get_token())
    (HERE/'verification'/'connected-graph.json').write_text(json.dumps(graph,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print('Connected original mission; root sketch status is recorded honestly.', flush=True)

if __name__ == '__main__':
    main()
