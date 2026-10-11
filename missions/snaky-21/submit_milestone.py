"""Submit one existing milestone after its local proof has passed."""
import argparse
import json
import re
import sys
from pathlib import Path
import publish

HERE=Path(__file__).resolve().parent
SPECS={
 'strategy':{
  'theorem_id':'ba8a045d-4e6e-478a-8e05-4c1527165825',
  'theorem_name':'OAI.SnakyConditional.snaky_winning_strategy_with_legal_states',
  'file':'milestone35-proof.lean',
  'log':'milestone-Strategy35.log',
  'explanation':
   'The previously proved 21-claim certificate supplies CanForce 21 from the empty board. '
   'Increasing the budget preserves this relation: induction keeps the same fresh first claim, '
   'and adds one to each continuation budget; an already won position remains won after a fresh claim, '
   'which exists on the infinite integer grid. Applying this monotonicity gives CanForce 35. '
   'The proved force_extract theorem then provides one globally fresh positional policy, '
   'a target after exactly 35 actual Maker claims, the required disjointness, and exact Breaker counts '
   'assuming legality of only the first 34 replies. The 35th Breaker reply is unconstrained. '
   'The captain\'s SnakyConditional game definitions are preserved; an induction identifies their '
   'playState with the identical SnakyPrototype recursion, and transports legality and the conclusion. '
   'Both imported support targets are already Proved. A separate closed local version uses the actual '
   'support proofs and has only the standard propext, Classical.choice and Quot.sound axioms. '
   'Source: https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/'
   'preprints/Snaky-in-21-Maker-moves-September-25-2026; the completed 21-move theorem implies '
   'this weaker 35-move game bound.'},
 'certificate':{
  'theorem_id':'c5e790f7-904e-40dd-a7f5-ba72d31e941b',
  'theorem_name':'OAI.SnakyCertificate.certificate_correct',
  'file':'milestone-certificate-proof.lean',
  'log':'milestone-Certificate35.log',
  'explanation':
   'This verifies the original 35-move certificate encoded in Definitions.Def_SnakyCertificate; '
   'it does not replace those data with the newer 21-move certificate. Each of the 616 row values is '
   'proved equal to an explicit finite required set, envelope, and height. For a nonbase row, '
   'the original table lookup is checked by kernel reduction, rowAt is unfolded once, and already '
   'proved child equalities reduce the goal to the exact printed orientation, translation and '
   'forkRow computation. Every remaining finite equality is checked by decide +kernel. '
   'The proof also checks the 610 nonbase entries, their ordered indices, nonempty term lists and '
   'strict backward references, and the total of 1837 placement terms. All 616 rows satisfy the '
   'subset, origin and height conditions. The four outputs are respectively (557,118,19), '
   '(595,222,27), (603,275,27) with required cell (-1,0), and (615,686,34) with required cell (1,0). '
   'Each omitted region is disjoint from the complete envelope, proved by a bounded universal '
   'check on its cells. Python generates the candidate literals and cross-checks the data; '
   'Lean independently proves their equality to the original recursive definitions. '
   'No native_decide, sorry, or new axiom is used. This finite-data milestone does not assume or '
   'assert the game-theoretic interpretation of conditional cards. '
   'Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/'
   'lean/ComparatorChallenges/SnakyCertificate.lean; Proposition 10, finite part.'}
}

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    p=argparse.ArgumentParser()
    p.add_argument('milestone',choices=SPECS)
    args=p.parse_args()
    spec=SPECS[args.milestone]
    log=HERE/'verification'/spec['log']
    if not log.exists() or 'depends on axioms:' not in log.read_text(encoding='utf-8'):
        raise RuntimeError('The actual closed proof has no completed axiom audit: '+str(log))
    audits=re.findall(r'depends on axioms: \[([^\]]*)\]',log.read_text(encoding='utf-8'))
    for audit in audits:
        unexpected={a.strip() for a in audit.split(',') if a.strip()}-{'propext','Classical.choice','Quot.sound'}
        if unexpected:
            raise RuntimeError('Unexpected local milestone axioms: '+str(unexpected))
    result=publish.submit(spec['theorem_id'],HERE/'platform'/spec['file'],
                          spec['explanation'],publish.api.get_token(),publish.read_journal(),
                          spec['theorem_name'])
    if result['status']!='ACCEPTED':
        raise RuntimeError('Milestone is not fully ACCEPTED: '+str(result['status']))
    print('MILESTONE ACCEPTED',spec['theorem_name'],flush=True)

if __name__=='__main__':
    main()
